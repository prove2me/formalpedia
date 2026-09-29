-- Prove2me | Theorems.Thm_mme_induced_graded_address_blocks_restrict
-- name    : mme_induced_graded_address_blocks_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T18:46:23.085821+00:00
-- url     : https://prove2.me/theorems/b733f18a-4aae-41fd-a2e9-e945c7328409
-- title:
--   Induced grading-word families restrict as a direct sum
-- statement:
--   Let $T$ be an order-three tensor with a $t$-class grading, and let $A_1,\ldots,A_k$ be length-$N$ addresses of grading triples. Assume the retained family is induced: whenever one independently chooses an address in each of the three modes and every resulting mixed coordinate block is nonzero, all three choices are the same address. Then variable zeroing extracts the retained address blocks as a genuine direct sum:
--
--   $$
--   \bigoplus_{j=1}^{k} B(A_j)\;\le\;T^{\otimes N}.
--   $$
--
--   The statement is valid for all natural numbers $N$ and $k$, including the empty boundary cases. It isolates the reusable tensor-algebra core of Salem--Spencer/laser-method pruning from the paper-specific counting argument.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), support-based variable zeroing and collision deletion on journal pp. 267--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_induced_word_zeroing
open MME
universe u

theorem mme_induced_graded_address_blocks_restrict
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t N k : ℕ}
    (G : T.TypeGrading t)
    (A : Fin k → Fin 3 → Fin N → Fin t)
    (hInduced : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i => A (js i) i r) ≠ 0) →
      ∃ j : Fin k, js = fun _ => j) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j => gradedAddressBlock G (A j)))
      (T.kronPow N) := by
  sorry
