-- Prove2me | solution 1 for two_oracle_mixed_implies_dictatorial
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:54:12.08973+00:00
-- url     : https://prove2.me/submissions/453d871f-393b-44bd-81d3-5be4c9b81ebe

-- Sol generated from Evergreen/Prediction/Impossibility.lean
import Mathlib
import Definitions.Def_Evergreen_Prediction_Impossibility
/-
  # Prediction Science: Impossibility Theorems

  The fundamental limits of prediction, formalized:
  1. No Free Lunch Theorem
  2. The Halting Problem as prediction impossibility
  3. Heisenberg-type uncertainty for predictions
  4. The Gödelian limit: self-referential prediction paradox
  5. Conservation of prediction difficulty
-/


open Set Function Finset

noncomputable section

/-! ## §1. No Free Lunch Theorem

Over all possible futures, no predictor is universally better than any other.
This is the prediction-theoretic analogue of Wolpert's NFL theorem. -/


/-! ## §2. The Halting Prediction Impossibility

No computable predictor can predict whether an arbitrary program halts.
We encode this as a diagonal argument. -/


/-! ## §3. Heisenberg Prediction Uncertainty

Prediction precision for conjugate observables is bounded. -/


/-! ## §4. The Gödelian Prediction Limit

A prediction system cannot predict a diagonalized version of itself.
This is the prediction-theoretic Gödel incompleteness. -/

/-
PROBLEM
The Gödelian diagonal: for any predictor that maps codes to outputs,
    there exists a function that differs from every predicted function
    at its own index. This is Cantor's theorem applied to prediction.

PROVIDED SOLUTION
Let f n = predict n n + 1. Then f n = predict n n + 1 ≠ predict n n since Nat.succ_ne_self. Use ⟨fun n => predict n n + 1, fun n => Nat.succ_ne_self _⟩.
-/

/-
PROBLEM
The liar's paradox for prediction: for any enumeration of
    predictors, there exists a function no predictor matches everywhere.
    This follows from the diagonal argument.

PROVIDED SOLUTION
Let f n = !(predictors n n). Then for any n, f n = !(predictors n n) ≠ predictors n n by Bool.not_ne_self or similar. Use ⟨fun n => !(predictors n n), fun n => Bool.not_ne_self _⟩ or ⟨fun n => !predictors n n, fun n => ...⟩.
-/

/-! ## §5. The Conservation of Prediction Difficulty

Total prediction difficulty is conserved: making one aspect more predictable
necessarily makes another less predictable (information-theoretic). -/


/-! ## §6. Arrow-type result: Dictatorial structure of binary aggregation

With 2 oracles, if the aggregation respects unanimity AND anti-unanimity
(both agree on false → aggregate false, both agree on true → aggregate true)
and is monotone, and the mixed profiles give opposite results,
then one oracle dictates. -/




/-
PROBLEM
With 2 oracles, if the two mixed profiles give different outputs,
    then the function is dictatorial. This is the core of Arrow's theorem
    in the binary prediction setting.

PROVIDED SOLUTION
There are exactly 4 profiles for 2 oracles: (T,T), (T,F), (F,T), (F,F). By unanimity, f(T,T) = T and f(F,F) = F. By hmixed, f(T,F) ≠ f(F,T). Since these are booleans, one is true and one is false. Case 1: f(T,F) = T, f(F,T) = F → oracle 0 is dictator. Case 2: f(T,F) = F, f(F,T) = T → oracle 1 is dictator. To show dictatorship, use Fin.forall_fin_two to check all 4 profiles. Use decide or native_decide for the finite case analysis.
-/


theorem solution    (f : SocialPredictionFn 2)
    (hunan : unanimous f)
    (hmixed : f (fun i => if i = 0 then true else false) ≠
              f (fun i => if i = 0 then false else true)) :
    dictatorial f := by
  cases em ( f ( fun i : Fin 2 => if i = 0 then true else false ) = true ) <;> cases em ( f ( fun i : Fin 2 => if i = 0 then false else true ) = true ) <;> simp_all +decide [ unanimous, funext_iff, Fin.forall_fin_two ];
  · use 0; intro profile; fin_cases profile <;> simp_all +decide [ Fin.forall_fin_two ] ;
    · convert hunan.1 using 1 ; congr ; ext i ; fin_cases i <;> rfl;
    · convert ‹ ( f fun i => decide ( i = 0 ) ) = true › using 1;
      exact congr_arg f ( by ext i; fin_cases i <;> rfl );
    · convert ‹ ( f fun i => !decide ( i = 0 ) ) = false › using 1;
      exact congr_arg f ( by ext i; fin_cases i <;> rfl );
    · convert hunan.2 using 2 ; ext i ; fin_cases i <;> rfl;
  · -- In this case, we can see that the second oracle is dictatorial.
    use 1
    intro profile
    by_cases h0 : profile 0 = true <;> by_cases h1 : profile 1 = true <;> simp_all +decide [ Fin.forall_fin_two ];
    · rw [ show profile = fun _ => true from funext fun i => by fin_cases i <;> assumption ] ; aesop;
    · convert ‹ ( f fun i : Fin 2 => decide ( i = 0 ) ) = false › using 2 ; ext i ; fin_cases i <;> simp +decide [ * ];
    · convert ‹f ( fun i => !decide ( i = 0 ) ) = true› using 2 ; ext i ; fin_cases i <;> simp +decide [ * ];
    · convert hunan.2 using 2 ; ext i ; fin_cases i <;> aesop
