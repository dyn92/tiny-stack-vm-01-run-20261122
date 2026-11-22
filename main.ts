// Tiny stack VM for make.fun tiny-stack-vm-01 (ISA.md in the kit).
// One run answers every instance in /input, writing /output/<id>/stdout.bin
// and /output/<id>/exit.txt. Arithmetic wraps to 32 bits; a trap ends a
// program at once and keeps the output written before it.
import { mkdirSync as M, readFileSync as R, readdirSync as D, writeFileSync as W } from 'node:fs';
import { join as J } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
// Per-opcode shape: immediate bytes, values popped, values pushed.
// Opcodes the ISA never names stay unknown (K 0).
const IM = new Uint8Array(256), PO = new Uint8Array(256), PU = new Uint8Array(256), K = new Uint8Array(256);
function S(o: number, i: number, p: number, u: number): void { IM[o] = i; PO[o] = p; PU[o] = u; K[o] = 1; }
S(0, 0, 0, 0); S(1, 1, 0, 1); S(2, 4, 0, 1); S(3, 0, 1, 0); S(4, 0, 1, 2); S(5, 0, 2, 2);
S(6, 0, 2, 3); S(7, 0, 3, 3);
S(16, 0, 2, 1); S(17, 0, 2, 1); S(18, 0, 2, 1); S(19, 0, 2, 1); S(20, 0, 2, 1); S(21, 0, 2, 1);
S(22, 0, 2, 1); S(23, 0, 1, 1); S(24, 0, 2, 1); S(25, 0, 2, 1); S(26, 0, 2, 1); S(27, 0, 1, 1);
S(28, 0, 2, 1); S(29, 0, 2, 1); S(30, 0, 2, 1); S(32, 0, 2, 1); S(33, 0, 2, 1); S(34, 0, 2, 1);
S(48, 2, 0, 0); S(49, 2, 1, 0); S(50, 2, 1, 0); S(51, 2, 0, 0); S(52, 0, 0, 0);
S(64, 0, 1, 1); S(65, 0, 2, 0); S(80, 0, 1, 0); S(81, 0, 1, 0); S(82, 0, 0, 1); S(83, 0, 1, 0);

function run(p: Uint8Array, g: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  const s = new Int32Array(256), c = new Int32Array(64), m = new Int32Array(256);
  const o = new Uint8Array(65536);
  let sp = 0, cp = 0, pc = 0, st = 0, ol = 0, ip = 0;
  const f = (x: number): { out: Uint8Array; code: number } => ({ out: o.slice(0, ol), code: x });
  for (;;) {
    if (st === 1000000) return f(10); // step limit, checked first
    if (pc < 0 || pc >= n) return f(9); // pc outside the program
    const op = p[pc];
    if (!K[op]) return f(5); // unknown opcode
    const im = IM[op];
    if (pc + im >= n) return f(9); // immediate cut off by the end
    st++;
    const nx = pc + 1 + im;
    if (sp < PO[op]) return f(2); // stack underflow
    if (sp - PO[op] + PU[op] > 256) return f(3); // stack overflow
    pc = nx;
    if (op === 0) return f(0); // HALT
    else if (op === 1) s[sp++] = (p[nx - 1] << 24) >> 24; // PUSH8, sign-extended
    else if (op === 2) s[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); // PUSH32 LE
    else if (op === 3) sp--; // POP
    else if (op === 4) { s[sp] = s[sp - 1]; sp++; } // DUP
    else if (op === 5) { const t = s[sp - 1]; s[sp - 1] = s[sp - 2]; s[sp - 2] = t; } // SWAP
    else if (op === 6) { s[sp] = s[sp - 2]; sp++; } // OVER
    else if (op === 7) { const a = s[sp - 3]; s[sp - 3] = s[sp - 2]; s[sp - 2] = s[sp - 1]; s[sp - 1] = a; } // ROT
    else if (op === 23) s[sp - 1] = (-s[sp - 1]) | 0; // NEG
    else if (op === 27) s[sp - 1] = ~s[sp - 1]; // NOT
    else if (op < 35) { // binary ops 16-22, 24-26, 28-30, 32-34
      const b = s[sp - 1], a = s[sp - 2];
      let r: number;
      if (op === 16) r = (a + b) | 0;
      else if (op === 17) r = (a - b) | 0;
      else if (op === 18) r = Math.imul(a, b);
      else if (op === 19) { if (!b) return f(4); r = (a / b) | 0; } // DIV, truncates toward zero
      else if (op === 20) { if (!b) return f(4); r = b === -1 ? 0 : (a % b) | 0; } // MOD, sign of a
      else if (op === 21) { if (!b) return f(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; } // DIVU
      else if (op === 22) { if (!b) return f(4); r = ((a >>> 0) % (b >>> 0)) | 0; } // MODU
      else if (op === 24) r = a & b;
      else if (op === 25) r = a | b;
      else if (op === 26) r = a ^ b;
      else if (op === 28) r = a << (b & 31);
      else if (op === 29) r = a >> (b & 31);
      else if (op === 30) r = (a >>> (b & 31)) | 0;
      else if (op === 32) r = a === b ? 1 : 0;
      else if (op === 33) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
      sp -= 2;
      s[sp++] = r;
    } else if (op < 51) { // JMP / JZ / JNZ, signed 16-bit offset from next instruction
      const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
      let t = true;
      if (op !== 48) { const v = s[--sp]; t = op === 49 ? v === 0 : v !== 0; }
      if (t) pc = nx + rel;
    } else if (op === 51) { // CALL, unsigned 16-bit target
      if (cp === 64) return f(7);
      c[cp++] = nx;
      pc = p[nx - 2] | (p[nx - 1] << 8);
    } else if (op === 52) { // RET
      if (!cp) return f(8);
      pc = c[--cp];
    } else if (op === 64) { // LOAD
      const a = s[sp - 1];
      if (a < 0 || a > 255) return f(6);
      s[sp - 1] = m[a];
    } else if (op === 65) { // STORE: stack is ( v addr -- ), addr on top
      const a = s[sp - 1], v = s[sp - 2];
      if (a < 0 || a > 255) return f(6);
      sp -= 2;
      m[a] = v;
    } else if (op === 80) { // PRINT: decimal ASCII, no newline
      const t = String(s[sp - 1]);
      if (ol + t.length > 65536) return f(11);
      sp--;
      for (let i = 0; i < t.length; i++) o[ol++] = t.charCodeAt(i);
    } else if (op === 81) { // PUTC: one byte, low 8 bits
      if (ol + 1 > 65536) return f(11);
      o[ol++] = s[--sp] & 255;
    } else if (op === 82) { // IN: next input byte, or -1 once used up
      s[sp++] = ip < g.length ? g[ip++] : -1;
    } else return f(s[--sp] & 255); // EXIT: low byte of the popped value
  }
}

for (const id of D(I).sort()) {
  let g: Uint8Array;
  try { g = R(J(I, id, 'input.bin')); } catch { g = new Uint8Array(0); }
  const r = run(R(J(I, id, 'program.bin')), g);
  M(J(O, id), { recursive: true });
  W(J(O, id, 'stdout.bin'), r.out);
  W(J(O, id, 'exit.txt'), r.code + '\n');
}
