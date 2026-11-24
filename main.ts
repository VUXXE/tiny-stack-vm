// Tiny stack VM: an exact implementation of make.fun's tiny stack ISA v1
// (program/generator/subject/ISA.md). Written from the ISA spec; plain
// JavaScript, Node 22 stdlib only. Reads /input/<id>/{program,input}.bin,
// writes /output/<id>/{stdout.bin,exit.txt} for every instance in one run.
//
// Dispatch is table-driven: OPS[byte] = [immediate bytes, pops, pushes].
// The fetch sequence follows ISA.md "One step" in its numbered order:
// step limit, pc outside, unknown opcode, immediate cut off, then one
// uniform stack check (underflow, then overflow) before the instruction's
// own traps. No opcode repeats its own stack check: the table carries
// what each instruction pops and pushes, so the order the spec states is
// the order the code checks. Opcode 0x1f is deliberately absent from the
// table (no such opcode), so it traps 5 like any unknown byte.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// [immediate bytes, pops, pushes] per opcode; a missing entry is unknown.
const OPS = {
  0x00: [0,0,0], 0x01: [1,0,1], 0x02: [4,0,1], 0x03: [0,1,0],
  0x04: [0,1,2], 0x05: [0,2,2], 0x06: [0,2,3], 0x07: [0,3,3],
  0x10: [0,2,1], 0x11: [0,2,1], 0x12: [0,2,1], 0x13: [0,2,1],
  0x14: [0,2,1], 0x15: [0,2,1], 0x16: [0,2,1], 0x17: [0,1,1],
  0x18: [0,2,1], 0x19: [0,2,1], 0x1a: [0,2,1], 0x1b: [0,1,1],
  0x1c: [0,2,1], 0x1d: [0,2,1], 0x1e: [0,2,1],
  0x20: [0,2,1], 0x21: [0,2,1], 0x22: [0,2,1],
  0x30: [2,0,0], 0x31: [2,1,0], 0x32: [2,1,0], 0x33: [2,0,0],
  0x34: [0,0,0],
  0x40: [0,1,1], 0x41: [0,2,0],
  0x50: [0,1,0], 0x51: [0,1,0], 0x52: [0,0,1], 0x53: [0,1,0],
};

function run(p, inp) {
  const n = p.length;
  const D = new Int32Array(256); // data stack
  const C = new Int32Array(64); // call stack
  const M = new Int32Array(256); // memory
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, st = 0;
  const end = (code) => [out.subarray(0, ol), code];
  for (;;) {
    if (st === 1e6) return end(10); // 1. step limit
    if (pc < 0 || pc >= n) return end(9); // 2. pc outside program
    const op = p[pc];
    const e = OPS[op];
    if (!e) return end(5); // 3. unknown opcode
    const im = e[0];
    if (pc + im >= n) return end(9); // 4. immediate cut off by program end
    st++;
    if (sp < e[1]) return end(2); // 5. stack underflow
    if (sp - e[1] + e[2] > 256) return end(3); // 5. stack overflow
    pc += 1 + im;
    if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b) {
      const b = D[sp - 1], a = D[sp - 2];
      let r;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b); // low 32 bits, exact
      else if (op === 0x13) { if (!b) return end(4); r = (a / b) | 0; }
      else if (op === 0x14) { if (!b) return end(4); r = (a % b) | 0; }
      else if (op === 0x15) { if (!b) return end(4); r = ((a >>> 0) / (b >>> 0)) | 0; }
      else if (op === 0x16) { if (!b) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
      else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = a >>> (b & 31);
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
      sp--;
      D[sp - 1] = r;
      continue;
    }
    switch (op) {
      case 0x00: return end(0); // HALT
      case 0x01: // PUSH8, sign-extended
        D[sp++] = (p[pc - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32, little-endian
        D[sp++] = p[pc - 4] | (p[pc - 3] << 8) | (p[pc - 2] << 16) | (p[pc - 1] << 24);
        break;
      case 0x03: // POP
        sp--;
        break;
      case 0x04: // DUP
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 0x05: { // SWAP
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 0x06: // OVER
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 0x07: { // ROT
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 0x17: // NEG
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 0x1b: // NOT
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x30: // JMP (signed 16-bit offset from next instruction)
        pc += ((p[pc - 2] | (p[pc - 1] << 8)) << 16) >> 16;
        break;
      case 0x31: // JZ
      case 0x32: { // JNZ
        const v = D[--sp];
        if ((op === 0x31) === (v === 0)) pc += ((p[pc - 2] | (p[pc - 1] << 8)) << 16) >> 16;
        break;
      }
      case 0x33: // CALL (unsigned 16-bit target)
        if (cp === 64) return end(7);
        C[cp++] = pc;
        pc = p[pc - 2] | (p[pc - 1] << 8);
        break;
      case 0x34: // RET
        if (!cp) return end(8);
        pc = C[--cp];
        break;
      case 0x40: { // LOAD
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: { // STORE (v addr --)
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        M[a] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT (decimal ASCII, no newline)
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC (low byte)
        if (ol === 65536) return end(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 0x52: // IN (next byte, -1 when exhausted)
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53: // EXIT (low byte)
        return end(D[--sp] & 255);
      default: return end(5); // unreachable: unknown opcodes trap above
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const rd = (f) => { try { return readFileSync(f); } catch { return Buffer.alloc(0); } };
for (const id of readdirSync(I).sort()) {
  const [o, code] = run(rd(join(I, id, 'program.bin')), rd(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), o);
  writeFileSync(join(O, id, 'exit.txt'), code + '\n');
}
