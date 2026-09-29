-- Prove2me | Definitions.Def_Applications_StackSorting_StackSortMap
-- name    : Applications_StackSorting_StackSortMap
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:59.614377+00:00
-- url     : https://prove2.me/theorems/bcd4f232-b606-437b-bc1c-cae7ab2bcccc
-- title:
--   Aether Catalog definitions — Applications_StackSorting_StackSortMap
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.StackSorting.StackSortMap`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/StackSorting/StackSortMap.lean by skeleton subtraction
import Mathlib
/-
# West's stack-sorting map, as an executable function on lists

We give a clean, structurally-recursive implementation of *West's stack-sorting
map* `s` (West 1990) and prove its fundamental structural properties.

The map is realised by the classical one-pass stack-sorting machine: scan the
input left to right keeping a stack (head = top); before reading a new entry
`x`, pop every stack entry strictly smaller than `x` to the output, then push
`x`; when the input is exhausted, flush the stack to the output.  This one pass
is exactly West's map `s`, and iterating it sorts any permutation — the
*stack-sorting depth* of a permutation is the number of iterations required.

## Main results

* `stackSort_perm` : `stackSort l` is a permutation of `l` (the map only
  rearranges, it never loses or invents entries).
* `stackSort_length` : the map preserves length.
* `stackSort_sorted_fixed` : a strictly increasing list is a fixed point — once
  sorted, further passes do nothing, so its stack-sorting depth is `0`.

The worked example `stackSort [2,3,1] = [2,1,3]` (still unsorted) together with
`stackSort [2,1,3] = [1,2,3]` exhibits a permutation of stack-sorting depth
exactly `2`, the smallest depth-`2` permutation; this is the combinatorial seed
of the average-depth statistic `D_n` studied by Defant.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): West's map can be implemented by a *structurally*
  recursive stack machine (recursion on the remaining input), avoiding the
  well-founded "split at the maximum" recursion, and the two load-bearing
  invariants are (a) the map is a permutation of its input and (b) sorted
  inputs are fixed points.
Experiment (Experimenter): Defined `stackStep`/`stackGo`/`stackSort`; checked
  by `#eval` that `[2,3,1] ↦ [2,1,3] ↦ [1,2,3]` and that decreasing inputs
  sort in a single pass. Proved the permutation invariant by induction (via the
  per-step lemma `stackStep_perm`) and the fixed-point property via the
  auxiliary single-element-stack lemma `stackGo_singleton_sorted`.
Analysis (Analyst): Permutation + length are robust and reusable. The
  fixed-point lemma needed the *strict* order `<` (with duplicates an equal
  entry is pushed rather than popped, so `≤`-sortedness is not preserved by the
  single-pass machine in the naive statement); restricting to strict order
  (the relevant case for genuine permutations) makes it clean.
Critique (Critic): `stackSort_perm` and `stackSort_sorted_fixed` are proved by
  genuine induction, not `decide`. The concrete depth-2 witness is recorded as
  an `example` (illustration), not as a main theorem, so the anti-trivial
  guardrails are respected. Corner case checked: empty list and singleton.
Synthesis (PI): These give a verified, executable substrate on which the depth
  statistic `D_n` and Defant's bound can later be formalized.
-/

namespace Applications.StackSorting

/-- One step of the stack machine on stack `stk` (head = top) reading entry `x`:
pop all entries strictly below `x`, then push `x`.  Returns the popped output
(in pop order) together with the new stack. -/
def stackStep : List ℕ → ℕ → (List ℕ × List ℕ)
  | [], x => ([], [x])
  | (t :: ts), x =>
      if t < x then
        let r := stackStep ts x
        (t :: r.1, r.2)
      else ([], x :: t :: ts)

/-- Run the stack machine over the remaining input `l` starting from stack
`stk`; flush the stack at the end. -/
def stackGo : List ℕ → List ℕ → List ℕ
  | stk, [] => stk
  | stk, (x :: xs) =>
      let r := stackStep stk x
      r.1 ++ stackGo r.2 xs

/-- West's stack-sorting map `s` as one pass of the machine from the empty
stack. -/
def stackSort (l : List ℕ) : List ℕ := stackGo [] l

/-
A single machine step rearranges `x :: stk`: the popped output followed by
the new stack is a permutation of pushing `x` onto `stk`.
-/

/-
Running the machine from stack `stk` over input `l` yields a permutation of
`stk ++ l`.
-/

/-
**West's map only permutes:** `stackSort l` is a permutation of `l`.
-/


/-
Auxiliary fixed-point lemma: if `l` is strictly increasing and `a` is below
every entry of `l`, the machine started with the single-element stack `[a]`
returns `a :: l` unchanged.
-/

/-
**Sorted inputs are fixed points:** a strictly increasing list is left
unchanged by West's map, hence has stack-sorting depth `0`.
-/

end Applications.StackSorting


