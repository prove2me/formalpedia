-- Prove2me | Theorems.Thm_mme_CW_primary_hash_Ctensor_outer_middle_certificates
-- name    : mme_CW_primary_hash_Ctensor_outer_middle_certificates
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-07T14:47:39.791299+00:00
-- url     : https://prove2.me/theorems/8ef76a02-b8bf-44ea-9e10-7f95c2c8e84d
-- title:
--   Hash-family certificates for the coupled constituent at every q
-- statement:
--   Hash-family certificates for the coupled Coppersmith--Winograd constituent, at every $q$.
--
--   Eventually in $N$, on the floor profile $L=\lfloor 2N/(q^{3\tau}+2)\rfloor$, $G=N-L$ satisfying the pruning conditions, there are $A$ and $H$ with $0<H\le 4^N$ carrying a `CTensorOneHOneFamilyCertificate` for $(\mathrm{coupled}_q)^{\otimes 2N}$ with parameters $A$, $H$ and volume $q^{4G+2L}$, whose outer and middle counts satisfy
--   $$Z\,e^{-N\,\text{loss}/12}\le A,\qquad B\,e^{-N\,\text{loss}/8}\le 4X^2H .$$
--
--   Two observations make this general in $q$. First, the hash family itself (`CWQ6PrimaryHashFamily N L G A H`) is a purely combinatorial object built from Behrend sets and modular hashes: it records only $N$, $L$, $G$ and the two counts, and never mentions $q$. Second, the transport of such a family into an actual tensor certificate is `mme_coupled_four_block_induced_family_Ctensor_certificates_design`, which already takes $q$ as a parameter and produces volume $q^{4G+2L}$; its input is the four-block grading of the coupled constituent, supplied for every $q$ by `mme_CW_coupled_three_grading_isomorphism_certificate`.
--
--   So this is the $q=6$ node `mme_CW_q6_primary_hash_Ctensor_outer_middle_certificates` with $q$ left free; no hypothesis on $q$ is needed.
-- source:
--   Don Coppersmith and Shmuel Winograd, Matrix multiplication via arithmetic progressions, Journal of Symbolic Computation 9(3), 1990, 251-280; the coupled four-sum constituent (d) on printed p. 266 and its value lemma on printed p. 270. General-q form of the q=6 chain used for omega < 2.376.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_CW_coupled_value

open MME Filter Topology

universe u

theorem mme_CW_primary_hash_Ctensor_outer_middle_certificates
    {K : Type u} [Field K] (q : ℕ) (tau : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((q : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let Zcount : ℕ :=
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
      let Xcount : ℕ := Nat.choose N Gcount
      let middle : ℕ := Nat.choose (2 * Gcount) Gcount
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
      ∃ A H : ℕ,
        0 < H ∧
        H ≤ 4 ^ N ∧
        Nonempty
          (CTensorOneHOneFamilyCertificate
            ((coupledObj K q).kronPow (2 * N))
            A H (q ^ (4 * Gcount + 2 * L))) ∧
        (Zcount : ℝ) * Real.exp (-((N : ℝ) * loss / 12)) ≤
          (A : ℝ) ∧
        (middle : ℝ) * Real.exp (-((N : ℝ) * loss / 8)) ≤
          4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by
  sorry
