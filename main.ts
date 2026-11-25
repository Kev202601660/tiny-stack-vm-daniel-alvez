// tiny-stack-vm-01 entry: an interpreter of make.fun's tiny stack ISA (ISA.md), correct on every
// trap, limit and 32-bit corner, and small so it ties a perfect score at the smallest size.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// [immediate bytes, values popped, values pushed], by opcode.
const S: (number[] | undefined)[] = [];
const d = (o: number, i: number, a: number, b: number): void => void (S[o] = [i, a, b]);
d(0x00, 0, 0, 0); d(0x01, 1, 0, 1); d(0x02, 4, 0, 1); d(0x03, 0, 1, 0); d(0x04, 0, 1, 2);
d(0x05, 0, 2, 2); d(0x06, 0, 2, 3); d(0x07, 0, 3, 3);
d(0x10, 0, 2, 1); d(0x11, 0, 2, 1); d(0x12, 0, 2, 1); d(0x13, 0, 2, 1); d(0x14, 0, 2, 1);
d(0x15, 0, 2, 1); d(0x16, 0, 2, 1); d(0x17, 0, 1, 1); d(0x18, 0, 2, 1); d(0x19, 0, 2, 1);
d(0x1a, 0, 2, 1); d(0x1b, 0, 1, 1); d(0x1c, 0, 2, 1); d(0x1d, 0, 2, 1); d(0x1e, 0, 2, 1);
d(0x20, 0, 2, 1); d(0x21, 0, 2, 1); d(0x22, 0, 2, 1);
d(0x30, 2, 0, 0); d(0x31, 2, 1, 0); d(0x32, 2, 1, 0); d(0x33, 2, 0, 0); d(0x34, 0, 0, 0);
d(0x40, 0, 1, 1); d(0x41, 0, 2, 0); d(0x50, 0, 1, 0); d(0x51, 0, 1, 0); d(0x52, 0, 0, 1);
d(0x53, 0, 1, 0);

const enc = new TextEncoder();
const OUT_MAX = 65536;

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(OUT_MAX);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, steps = 0;
  const end = (code: number) => ({ out: out.slice(0, ol), code });
  for (;;) {
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const s = S[p[pc]];
    if (s === undefined) return end(5);
    const imm = s[0];
    if (pc + imm >= n) return end(9);
    steps++;
    const nx = pc + 1 + imm;
    if (sp < s[1]) return end(2);
    if (sp - s[1] + s[2] > 256) return end(3);
    const op = p[pc];
    pc = nx;
    switch (op) {
      case 0x00: return end(0);
      case 0x01: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const t = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = t; break; }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { if (b === 0) return end(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 0x14) { if (b === 0) return end(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 0x15) { if (b === 0) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (b === 0) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2; D[sp++] = r; break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let go = true;
        if (op !== 0x30) { const v = D[--sp]; go = op === 0x31 ? v === 0 : v !== 0; }
        if (go) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return end(7);
        C[cp++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8); break;
      case 0x34:
        if (cp === 0) return end(8);
        pc = C[--cp]; break;
      case 0x40: { const a = D[sp - 1]; if (a < 0 || a > 255) return end(6); D[sp - 1] = M[a]; break; }
      case 0x41: { const a = D[sp - 1]; if (a < 0 || a > 255) return end(6); sp -= 2; M[a] = D[sp]; break; }
      case 0x50: {
        const bs = enc.encode(String(D[sp - 1]));
        if (ol + bs.length > OUT_MAX) return end(11);
        sp--; out.set(bs, ol); ol += bs.length; break;
      }
      case 0x51: if (ol + 1 > OUT_MAX) return end(11); out[ol++] = D[--sp] & 255; break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 0x53: return end(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), String(r.code) + '\n');
}
