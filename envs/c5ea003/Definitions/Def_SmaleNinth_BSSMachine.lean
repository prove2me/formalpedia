-- Prove2me | Definitions.Def_SmaleNinth_BSSMachine
-- name    : SmaleNinth_BSSMachine
-- status  : Definition
-- author  : @ORdos
-- created : 2026-09-06T15:07:28.072357+00:00
-- url     : https://prove2.me/theorems/d1f138e0-5e6e-4adc-8344-a4b45726dd5b
-- title:
--   Blum–Shub–Smale machines over $\mathbb{R}$
-- statement:
--   A **machine over the real numbers**, in the sense of Blum, Shub and Smale, is the model of computation in which exact real arithmetic is available at unit cost. This module fixes one concrete such model.
--
--   **Configurations.** The memory is a **tape**, a bi-infinite family of real registers indexed by the integers, written $x = (x_k)_{k \in \mathbb{Z}}$ with $x_k \in \mathbb{R}$. A **configuration** is a pair consisting of a **program counter** $p \in \mathbb{N}$ and a tape.
--
--   **Programs.** A **program** is a finite list of instructions, each of one of the following kinds, where the addresses $d, i, j \in \mathbb{Z}$ are fixed inside the instruction:
--
--   - $x_d := c$, loading a **machine constant** $c \in \mathbb{R}$, which may be an arbitrary real number;
--   - $x_d := x_i \ast x_j$ for $\ast \in \{+, -, \times, \div\}$, an exact field operation on two registers;
--   - a **left shift** replacing the tape $x$ by $k \mapsto x_{k+1}$, and a **right shift** replacing it by $k \mapsto x_{k-1}$;
--   - a **sign-test branch**: if $x_i \le 0$ set the counter to a fixed target, otherwise advance it by one;
--   - the two halting instructions $\mathsf{accept}$ and $\mathsf{reject}$.
--
--   Every non-branching, non-halting instruction advances the counter by one. The shifts are what give a finite list of instructions, whose addresses are hard-coded, access to unboundedly many registers.
--
--   **Execution and cost.** One step executes the instruction at the current counter; a configuration whose counter carries $\mathsf{accept}$, carries $\mathsf{reject}$, or points past the end of the program is a fixed point, so execution simply stalls there. Running a program on an initial tape means iterating this step from counter $0$. A program **decides in time $T$ with verdict $\beta \in \{\text{true}, \text{false}\}$** if for some $t \le T$ the configuration after exactly $t$ steps has its counter on $\mathsf{accept}$ (when $\beta$ is true) or on $\mathsf{reject}$ (when $\beta$ is false). **Cost is the number of executed instructions**: one unit per arithmetic operation, constant load, shift, or comparison, irrespective of the magnitude of the reals involved. This is the point of the model — no bit lengths enter the accounting.
--
--   **Input convention for linear systems.** An instance of linear feasibility, given by $A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$, is presented on the tape as: cell $0$ holds $m$, cell $1$ holds $n$, cells $2, \dots, mn + 1$ hold the entries of $A$ in row-major order, cells $mn+2, \dots, mn+m+1$ hold $b$, and every remaining cell — including every negative one — holds $0$. The instance therefore occupies $mn + m + 2$ cells, the quantity in which running times are measured.
--
--   **Conventions and their cost.** Division is totalized as $x/0 = 0$ and the branch test is the non-strict $x_i \le 0$; both are harmless, since a program may guard divisions by sign tests at no asymptotic cost. Halting requires the counter to rest on an actual halting instruction: running off the end of the program is not a verdict. Crucially, a program is a *single finite list* with no dependence on $m$ or $n$, so any statement quantifying over programs quantifies over **uniform** algorithms; non-uniform families of decision trees, one per input size, are not expressible here, and it is exactly this restriction that makes polynomial-time questions in this model nontrivial.
-- source:
--   L. Blum, M. Shub, S. Smale, On a theory of computation and complexity over the real numbers, Bull. AMS 21(1):1-46, 1989, Section 1 (machines over R, state space R_infinity, computation/branch/shift nodes); S. Smale, Mathematical problems for the next century, Mathematical Intelligencer 20(2):7-15, 1998, Problem 9.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Logic.Function.Iterate

/-!
A register machine over the real numbers (Blum–Shub–Smale style), with
unit-cost exact real arithmetic — the model in which Smale poses his 9th
problem.

Source: S. Smale, *Mathematical problems for the next century*, Mathematical
Intelligencer 20(2):7–15, 1998, Problem 9: "Is there a polynomial-time
algorithm over the real numbers which decides the feasibility of the linear
system of inequalities $Ax \ge b$?" — where "algorithm over the real
numbers" is the machine model of L. Blum, M. Shub, S. Smale, *On a theory of
computation and complexity over the real numbers*, Bull. AMS 21(1):1–46,
1989.

The model formalized here:

- The machine state is a program counter together with a **bi-infinite tape**
  `ℤ → ℝ` of real registers (the state space `ℝ_∞` of BSS §1; a bi-infinite
  tape with two-sided shifts is the standard presentation giving full
  Turing-style access to unboundedly many registers).
- A program is a finite list of instructions. Arithmetic instructions
  (`const`, `add`, `sub`, `mul`, `div`) act on tape cells at **fixed**
  addresses hard-coded in the instruction — together with the two shift
  instructions this yields exactly the BSS computation nodes (rational maps
  with built-in real machine constants, applied in a finite window that the
  shifts move along the tape). `jle i target` is the BSS branch node
  (branch on the sign test `x_i ≤ 0`); `accept` / `reject` are output nodes.
- Division is Lean-total (`x / 0 = 0`), a benign totalization: a genuine BSS
  machine can guard every division by a sign test at no asymptotic cost.
- **Cost = number of executed instructions** (unit cost per arithmetic
  operation, comparison, or shift — the algebraic/arithmetic complexity
  measure). The input is `k` real numbers laid out in tape cells `0, …, k−1`;
  "polynomial time" means a step count polynomial in `k`.

`encodeLP` fixes the input convention for the LP feasibility problem: for an
`m × n` system `Ax ≥ b`, the tape holds `m` and `n` (as reals) in cells
`0, 1`, the entries of `A` row-major in cells `2, …, mn+1`, and `b` in cells
`mn+2, …, mn+m+1`; all other cells are `0`.
-/

namespace SmaleNinth

/-- An instruction of a BSS register machine over `ℝ`: real-constant loads,
field arithmetic on fixed tape addresses, two-sided tape shifts, a sign-test
branch, and the two output instructions. -/
inductive BSSInstr : Type
  /-- `x[dst] := c` — load a machine constant (an arbitrary real, per BSS). -/
  | const (dst : ℤ) (c : ℝ)
  /-- `x[dst] := x[i] + x[j]`. -/
  | add (dst i j : ℤ)
  /-- `x[dst] := x[i] − x[j]`. -/
  | sub (dst i j : ℤ)
  /-- `x[dst] := x[i] * x[j]`. -/
  | mul (dst i j : ℤ)
  /-- `x[dst] := x[i] / x[j]` (Lean-total: division by zero yields `0`). -/
  | div (dst i j : ℤ)
  /-- Shift the whole tape one cell to the left: new `x[k] = ` old `x[k+1]`. -/
  | shiftL
  /-- Shift the whole tape one cell to the right: new `x[k] = ` old `x[k−1]`. -/
  | shiftR
  /-- If `x[i] ≤ 0` jump to instruction `target`, else fall through. -/
  | jle (i : ℤ) (target : ℕ)
  /-- Halt and accept. -/
  | accept
  /-- Halt and reject. -/
  | reject

/-- A BSS program: a finite list of instructions, executed from position `0`. -/
abbrev BSSProgram := List BSSInstr

/-- A machine configuration: program counter and the real-register tape. -/
structure BSSConfig where
  /-- The program counter (an index into the program list). -/
  pc : ℕ
  /-- The bi-infinite tape of real registers. -/
  tape : ℤ → ℝ

/-- One execution step. A configuration whose `pc` carries `accept`/`reject`
(or points outside the program) is halted: the step leaves it unchanged. -/
noncomputable def BSSStep (P : BSSProgram) (s : BSSConfig) : BSSConfig :=
  match P[s.pc]? with
  | none => s
  | some ins =>
    match ins with
    | .const dst c => ⟨s.pc + 1, Function.update s.tape dst c⟩
    | .add dst i j => ⟨s.pc + 1, Function.update s.tape dst (s.tape i + s.tape j)⟩
    | .sub dst i j => ⟨s.pc + 1, Function.update s.tape dst (s.tape i - s.tape j)⟩
    | .mul dst i j => ⟨s.pc + 1, Function.update s.tape dst (s.tape i * s.tape j)⟩
    | .div dst i j => ⟨s.pc + 1, Function.update s.tape dst (s.tape i / s.tape j)⟩
    | .shiftL => ⟨s.pc + 1, fun k => s.tape (k + 1)⟩
    | .shiftR => ⟨s.pc + 1, fun k => s.tape (k - 1)⟩
    | .jle i target => if s.tape i ≤ 0 then ⟨target, s.tape⟩ else ⟨s.pc + 1, s.tape⟩
    | .accept => s
    | .reject => s

/-- The configuration reached after `t` steps of `P` from initial tape `x`
(program counter starting at `0`). -/
noncomputable def BSSRun (P : BSSProgram) (x : ℤ → ℝ) (t : ℕ) : BSSConfig :=
  (BSSStep P)^[t] ⟨0, x⟩

/-- The configuration `s` is halted with boolean output `b` — its program
counter carries `accept` (for `b = true`) or `reject` (for `b = false`).
Halted configurations are fixed points of `BSSStep`. -/
def BSSHaltedWith (P : BSSProgram) (s : BSSConfig) (b : Bool) : Prop :=
  P[s.pc]? = some (if b then BSSInstr.accept else BSSInstr.reject)

/-- `P`, run on initial tape `x`, halts with output `b` within `T` steps.
`T` is the unit-cost (arithmetic) running time bound. -/
def BSSDecidesInTime (P : BSSProgram) (x : ℤ → ℝ) (T : ℕ) (b : Bool) : Prop :=
  ∃ t ≤ T, BSSHaltedWith P (BSSRun P x t) b

/-- The `k`th entry of the row-major listing of a matrix (junk value `0` out
of range): `matrixEntryRM A (i*n + j) = A i j`. -/
noncomputable def matrixEntryRM {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (k : ℕ) : ℝ :=
  if h : k < m * n ∧ 0 < n then
    A ⟨k / n, by
        have h1 := h.1
        rw [Nat.mul_comm] at h1
        exact Nat.div_lt_of_lt_mul h1⟩
      ⟨k % n, Nat.mod_lt _ h.2⟩
  else 0

/-- The input tape encoding the LP feasibility instance `∃x, Ax ≥ b`:
cell `0` holds `m`, cell `1` holds `n`, cells `2, …, mn+1` hold `A`
row-major, cells `mn+2, …, mn+m+1` hold `b`, and every other cell is `0`.
The input occupies `mn + m + 2` cells. -/
noncomputable def encodeLP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : ℤ → ℝ :=
  fun k =>
    if k = 0 then (m : ℝ)
    else if k = 1 then (n : ℝ)
    else if 2 ≤ k ∧ k < 2 + (m : ℤ) * n then matrixEntryRM A (k - 2).toNat
    else if h : 2 + (m : ℤ) * n ≤ k ∧ k < 2 + (m : ℤ) * n + m then
      b ⟨(k - (2 + (m : ℤ) * n)).toNat, by omega⟩
    else 0

end SmaleNinth


