-- Prove2me | Theorems.Thm_KServer_chunk_regrid2
-- name    : KServer.chunk_regrid2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T20:47:38.719141+00:00
-- url     : https://prove2.me/theorems/171b12fb-35f2-4633-9788-2fbe6bf1852c
-- title:
--   Grid regrouping with exact window count
-- statement:
--   A strengthening of the grid-regrouping lemma for chunk systems that additionally records the exact number of output windows. Given a chunk system with sizes in $[c_A, c_B]$, expected total $T$, escape price $p_e$, and at least $M$ chunks, whose pathwise total mass never exceeds $2\\delta M$ and whose total has variance at most $V$, the chunks regroup along the cumulative-mass grid of mesh $2\\delta$ into a chunk system with **exactly** $M$ windows, sizes in $[0, 2\\delta + c_B]$, the same expected total $T$, escape price $p' \\ge p_e + 2\\delta + c_B$, a trivial initial history, and output variance at most $V' \\ge \\tfrac{5}{4}V + 20(2\\delta + c_B)\\mathbb{E}[T_\\omega]$. The exact window count $C'.m = M$ is needed downstream to bound range terms in variance estimates of systems built from the regrouped one.
-- source:
--   Bansal-Cohen-Ravi style randomized k-server lower bound: level recursion plumbing

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

namespace KServer

theorem chunk_regrid2 {X : Type*} [MetricSpace X] {s t : X}
    {cA cB T pe : ℝ} {mL : ℕ} (C : ChunkSystemB X s t cA cB T pe mL)
    {M : ℕ} {δ p' V V' : ℝ}
    (hMm : M ≤ C.m) (hM0 : 0 < M) (hδ : 0 < δ)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hcB2δ : cB ≤ 2 * δ) (hpe : 0 ≤ pe)
    (hp : pe + (2 * δ + cB) ≤ p')
    (hTmax : ∀ ω, (∑ i, C.size ω i) ≤ 2 * δ * M)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hV' : 5 / 4 * V
      + 20 * ((2 * δ + cB) * ∑ ω, C.P ω * ∑ i, C.size ω i) ≤ V') :
    ∃ C' : ChunkSystemB X s t 0 (2 * δ + cB) T p' M,
      C'.m = M ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V') := by sorry

end KServer
