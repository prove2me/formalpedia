-- Prove2me | solution 1 for Erdos390.WholePaper.exists_uniform_roughFixedHead_friableCount_shift_bound_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:46:38.329738+00:00
-- url     : https://prove2.me/submissions/2ddfa2d1-94b9-47b1-89ec-67c84f62924c

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006
import Theorems.Thm_Erdos390_Full_FriableAsymptotic_exists_uniform_friableCount_dickman_bound
import Theorems.Thm_Erdos390_WholePaper_roughFriableMain_fixedDivisorShift_compact


section
theorem Erdos390.WholePaper.roughFriableMain_fixedDivisorShift : Erdos390.RemainingAnalyticGoal008_023 := @Erdos390.WholePaper.roughFriableMain_fixedDivisorShift_compact
end
/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)











theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero























end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.Full.FriableAsymptotic -/
section


/-!
# Friable counts on the Erdős 390 scale

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's actual finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace Erdos390.Full.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale

/-! ## Quantitative prime-number input

The finite de Bruijn induction below needs a power-saving prime Stieltjes
estimate.  We derive it here from the audited medium-strength PNT, rather than
postulating a prime-distribution contract.  The exponential PNT remainder is
stronger than every fixed power of `1 / log x`.
-/



















































/-! ## Explicit regularity of the finite Dickman kernel -/









/-! ## The Dickman test weight in the prime recurrence -/

































/-- Exact Dickman formula on the initial face `u ≤ 1`.  The only discrepancy
between the real endpoint and the count is therefore the explicit floor used
to create `X`; no analytic error occurs here. -/
theorem friableCount_eq_dickman_initial {X y : ℕ} (hX : 0 < X)
    (hy : 1 < y) (hXy : X ≤ y) :
    (friableCount X y : ℝ) = (X : ℝ) * rho (dickmanU X y) := by
  rw [friableCount_eq_self hXy, rho_eq_one_of_le_one
    (dickmanU_le_one hX hy hXy)]
  ring

















/-! ## Explicit oscillation and Riemann error for the Dickman weight -/


open DickmanBasic






























/-! ## Quantitative PNT transfer for the Dickman prime weight

The following estimates combine the preceding Chebyshev--Stieltjes identity,
the audited medium PNT, and the explicit Dickman-weight oscillation bound.
They are the one-prime analytic input for the finite de Bruijn induction.
-/


















/-! ## Uniform floor stability for the recursive Dickman kernel -/
























































/-- Uniform Dickman estimate with the exact initial face included. -/
theorem exists_uniform_friableCount_dickman_bound_all_faces :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → 0 < X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |(friableCount X y : ℝ) - (X : ℝ) * rho (dickmanU X y)| ≤
        K * (X : ℝ) / Real.log (y : ℝ) := by
  obtain ⟨K, hK, Y₁, hmain⟩ :=
    exists_uniform_friableCount_dickman_bound
  refine ⟨K, hK, max 2 Y₁, ?_⟩
  intro X y hy hX hlog
  have hy2 : 2 ≤ y := (le_max_left 2 Y₁).trans hy
  have hY₁y : Y₁ ≤ y := (le_max_right 2 Y₁).trans hy
  by_cases hyX : y ≤ X
  · exact hmain hY₁y hyX hlog
  · have hXy : X ≤ y := le_of_not_ge hyX
    rw [friableCount_eq_dickman_initial hX (by omega) hXy,
      sub_self, abs_zero]
    positivity




end Erdos390.Full.FriableAsymptotic

end

/- Source module: Erdos390.WholePaper.RoughHeadCompatibleFinitePoint -/
section


/-!
# The literal head-compatible finite raw point

This file constructs the first finite point in the guarded rough selector.
The upper block `E`, the high lower block `H`, and the broad lower block `J`
are literal natural-number half-open intervals.  Head freedom is imposed by
coprimality with the product of all primes up to `W`, and the raw weight is
defined pointwise from those finite sets.

The second half proves the exact deterministic identities used before any
HT--Saias or prime-number estimate: finite Möbius inclusion--exclusion,
reindexing of smooth multiples by division, and the resulting physical-block
shift through every divisor of the head modulus.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Literal physical intervals -/





















/-! ## The finite head and raw weights -/









/-- The head modulus is always positive, including for an empty head. -/
theorem roughHeadModulus_pos (W : ℕ) :
    0 < roughHeadModulus W := by
  rw [← roughHeadZeroPattern_modulus]
  exact Nat.pos_of_ne_zero (roughHeadZeroPattern W).modulus_ne_zero







































/-! ## Exact head inclusion--exclusion and smooth physical shifts -/

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughFixedHeadFriableShift -/
section


/-!
# The strongest available unconditional fixed-head friable shift

The paper uses the Hildebrand--Tenenbaum--Saias transition estimate to
obtain an `O_W(x / log(y)^2 + 1)` shift for a balanced physical block.
That transition estimate is not present in Mathlib, PrimeNumberTheoremAnd,
or the current project.  What *is* present is the closed uniform de Bruijn
estimate

`|Psi(X,y) - X * rho(log X / log y)| <= K * X / log y`

from `Full.FriableAsymptotic`.  This file records the strongest genuine
fixed-head consequence of that theorem.  It proves, without an analytic
hypothesis, an `O_W(X / log y + 1)` shift for the endpoint count, the
literal two-piece physical block, and its complete head Mobius closure.

The first lemma extends the already-proved floor-stability argument from
the recursive four-mark range `u <= 4` to the full endpoint range `u <= 5`.
It uses only the project's proved one-Lipschitz estimate for `rho`.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Full-range floor stability of the Dickman main term -/



/-! ## A fixed-divisor shift for the Dickman main term -/



/-! ## The closed fixed-head endpoint theorem -/

/-- Uniformly over every divisor of the fixed head modulus, the genuine
friable endpoint count at `floor(X/d)` is `1/d` times the count at `X`,
up to `O_W(X / log y + 1)`.  The constants and threshold are chosen before
`X`, `y`, and the head divisor. -/
theorem exists_uniform_roughFixedHead_friableCount_shift_bound
    (W : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y d : ℕ},
      Y₀ ≤ y →
      d ∈ (roughHeadModulus W).divisors →
      d ≤ X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |(FriableAsymptotic.friableCount (X / d) y : ℝ) -
          (FriableAsymptotic.friableCount X y : ℝ) / (d : ℝ)| ≤
        K * (X : ℝ) / ((d : ℝ) * Real.log (y : ℝ)) + 3 := by
  obtain ⟨K₀, hK₀, Y₁, hdeBruijn⟩ :=
    FriableAsymptotic.exists_uniform_friableCount_dickman_bound_all_faces
  let P : ℕ := roughHeadModulus W
  let K : ℝ := 2 * K₀ + Real.log (P : ℝ)
  let Y₀ : ℕ := max 2 Y₁
  have hP : 0 < P := by
    simpa only [P] using roughHeadModulus_pos W
  have hlogP : 0 ≤ Real.log (P : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ P by omega))
  have hK : 0 < K := by
    dsimp [K]
    linarith
  refine ⟨K, hK, Y₀, ?_⟩
  intro X y d hY hdMem hdX hlogX
  have hy2 : 2 ≤ y :=
    (le_max_left 2 Y₁).trans (by simpa only [Y₀] using hY)
  have hY₁ : Y₁ ≤ y :=
    (le_max_right 2 Y₁).trans (by simpa only [Y₀] using hY)
  have hdPos : 0 < d := by
    exact Nat.pos_of_mem_divisors (by simpa only [P] using hdMem)
  have hdDvd : d ∣ P := by
    exact (Nat.mem_divisors.mp (by simpa only [P] using hdMem)).1
  have hdP : d ≤ P := Nat.le_of_dvd hP hdDvd
  have hXPos : 0 < X := hdPos.trans_le hdX
  have hAPos : 0 < X / d := by
    apply Nat.div_pos
    exact hdX
    exact hdPos
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hAleX : X / d ≤ X := Nat.div_le_self X d
  have hlogA :
      Real.log ((X / d : ℕ) : ℝ) ≤ 5 * Real.log (y : ℝ) := by
    have hmono :
        Real.log ((X / d : ℕ) : ℝ) ≤ Real.log (X : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast hAPos
      · exact_mod_cast hAleX
    exact hmono.trans hlogX
  have hsmall := hdeBruijn hY₁ hAPos hlogA
  have hlarge := hdeBruijn hY₁ hXPos hlogX
  have hsmall' :
      |(FriableAsymptotic.friableCount (X / d) y : ℝ) -
          ((X / d : ℕ) : ℝ) *
            rho (FriableAsymptotic.dickmanU (X / d) y)| ≤
        K₀ * (X : ℝ) / ((d : ℝ) * Real.log (y : ℝ)) := by
    calc
      _ ≤ K₀ * ((X / d : ℕ) : ℝ) / Real.log (y : ℝ) := hsmall
      _ ≤ K₀ * ((X : ℝ) / (d : ℝ)) / Real.log (y : ℝ) := by
        gcongr
        exact Nat.cast_div_le
      _ = K₀ * (X : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) := by ring
  have hlarge' :
      |(((X : ℝ) * rho (FriableAsymptotic.dickmanU X y)) -
          (FriableAsymptotic.friableCount X y : ℝ)) / (d : ℝ)| ≤
        K₀ * (X : ℝ) / ((d : ℝ) * Real.log (y : ℝ)) := by
    rw [abs_div, abs_of_pos (by exact_mod_cast hdPos : (0 : ℝ) < d),
      abs_sub_comm]
    calc
      |(FriableAsymptotic.friableCount X y : ℝ) -
          (X : ℝ) * rho (FriableAsymptotic.dickmanU X y)| / (d : ℝ) ≤
        (K₀ * (X : ℝ) / Real.log (y : ℝ)) / (d : ℝ) := by
          exact (div_le_div_iff_of_pos_right
            (by exact_mod_cast hdPos : (0 : ℝ) < d)).2 hlarge
      _ = K₀ * (X : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) := by ring
  have hmodel := roughFriableMain_fixedDivisorShift
    hy2 hdPos hdX hlogX
  let smallError : ℝ :=
    (FriableAsymptotic.friableCount (X / d) y : ℝ) -
      ((X / d : ℕ) : ℝ) *
        rho (FriableAsymptotic.dickmanU (X / d) y)
  let modelError : ℝ :=
    ((X / d : ℕ) : ℝ) *
        rho (FriableAsymptotic.dickmanU (X / d) y) -
      ((X : ℝ) * rho (FriableAsymptotic.dickmanU X y)) / (d : ℝ)
  let largeError : ℝ :=
    (((X : ℝ) * rho (FriableAsymptotic.dickmanU X y)) -
      (FriableAsymptotic.friableCount X y : ℝ)) / (d : ℝ)
  have hrearrange :
      (FriableAsymptotic.friableCount (X / d) y : ℝ) -
          (FriableAsymptotic.friableCount X y : ℝ) / (d : ℝ) =
        smallError + (modelError + largeError) := by
    dsimp [smallError, modelError, largeError]
    ring
  rw [hrearrange]
  have hlogdP : Real.log (d : ℝ) ≤ Real.log (P : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hdPos
    · exact_mod_cast hdP
  have hscale :
      0 ≤ (X : ℝ) / ((d : ℝ) * Real.log (y : ℝ)) := by positivity
  calc
    |smallError + (modelError + largeError)| ≤
        |smallError| + (|modelError| + |largeError|) := by
      exact (abs_add_le _ _).trans
        (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ K₀ * (X : ℝ) / ((d : ℝ) * Real.log (y : ℝ)) +
        ((3 + (X : ℝ) * Real.log (d : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ))) +
        K₀ * (X : ℝ) / ((d : ℝ) * Real.log (y : ℝ))) := by
      exact add_le_add hsmall' (add_le_add hmodel hlarge')
    _ = (2 * K₀ + Real.log (d : ℝ)) * (X : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) + 3 := by ring
    _ ≤ (2 * K₀ + Real.log (P : ℝ)) * (X : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) + 3 := by
      gcongr
    _ = K * (X : ℝ) /
          ((d : ℝ) * Real.log (y : ℝ)) + 3 := by rfl

/-! ## Literal two-piece physical blocks -/





/-! ## Complete head Mobius closure at the available scale -/





end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_013 := by
  exact @Erdos390.WholePaper.exists_uniform_roughFixedHead_friableCount_shift_bound
