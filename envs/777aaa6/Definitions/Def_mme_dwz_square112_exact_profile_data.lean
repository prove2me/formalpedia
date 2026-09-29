-- Prove2me | Definitions.Def_mme_dwz_square112_exact_profile_data
-- name    : mme_dwz_square112_exact_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-07T07:10:30.964718+00:00
-- url     : https://prove2.me/theorems/49aaeb9a-ebc2-471e-9310-97edb2a1c2b7
-- title:
--   Literal four-row square112 exact profiles and marginal words
-- statement:
--   The canonical CW-square component $(1,1,2)$ has the four left fine split rows
--
--   $$(0,0,2),\quad(0,1,1),\quad(1,0,1),\quad(1,1,0),$$
--
--   in the released consumer order; the right row is $(1,1,2)$ minus the left. For arbitrary nonnegative integer multiplicities $c_0,c_1,c_2,c_3$, the data record the explicit X, Y, and Z marginal counts. An exact word is an actual length-$N$ word in these four labels having exactly these multiplicities; its mode word reads one coordinate at every position. These are lightweight finite combinatorial data for the symmetric-hashing construction. No count, uniformity, tensor extraction, value bound, balanced-family range or corner-equality hypothesis is part of the data. When composing the eventual tensor extraction, the row order must be identified with the canonical fine-word labels; no source isomorphism is assumed here.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173v5, Lemma3.6 and Section3.10 (printedpp22,24–27), Definition3.9 and Section6.3 (printedpp23–24,59); literal square112 support from the canonical CW-square decomposition. The released power4_dup_2.371919.mat SHA2562aa5713eb352bc94c939d340743c4107b42d274c9fa2058ff879cd7603142aeb uses this row order, including consumer-specific square69. The definition is generic in four multiplicities rather than fixed floating data.

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZSquare112

/-- The literal left fine split rows of canonical CW-square112, in the
released consumer order. The right row is 112 minus this row. -/
def row : Fin 4 → Fin 3 → Fin 3 :=
  ![![0, 0, 2], ![0, 1, 1], ![1, 0, 1], ![1, 1, 0]]

/-- Exact marginal multiplicities of the four literal rows. -/
def marginal (c : Fin 4 → ℕ) : Fin 3 → Fin 3 → ℕ :=
  ![![c 0 + c 1, c 2 + c 3, 0],
    ![c 0 + c 2, c 1 + c 3, 0],
    ![c 3, c 1 + c 2, c 0]]

/-- An actual word in the four square112 split rows with prescribed counts.
No tensor extraction or counting conclusion is a field of this subtype. -/
def ExactWord (N : ℕ) (c : Fin 4 → ℕ) : Type :=
  {w : Fin N → Fin 4 // ∀ r : Fin 4, Fintype.card {j : Fin N // w j = r} = c r}

/-- The literal fine-grade word seen by a particular mode of an exact word. -/
def modeWord {N : ℕ} {c : Fin 4 → ℕ} (w : ExactWord N c)
    (i : Fin 3) : Fin N → Fin 3 :=
  fun j ↦ row (w.1 j) i

end MME.DWZSquare112


