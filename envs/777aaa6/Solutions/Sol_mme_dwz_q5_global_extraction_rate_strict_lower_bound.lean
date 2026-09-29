-- Prove2me | solution 1 for mme_dwz_q5_global_extraction_rate_strict_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T18:21:26.824867+00:00
-- url     : https://prove2.me/submissions/2efa99e9-97e2-4996-a0c8-d7fbff350f0e

import Definitions.Def_mme_dwz_q5_global_asymptotic_data
import Theorems.Thm_mme_dwz_q5_exact_global_profile_certificate
import Theorems.Thm_mme_dwz_fourth_exact_scalar_certificate
import Theorems.Thm_mme_dwz_q5_coarse_entropy_lower_bounds
import Mathlib.Tactic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort

open BigOperators MME MME.DWZQ5ExactData MME.DWZQ5AsymptoticData
open MME.DWZFourthGlobalWitness MME.DWZFourthExactScalarCertificate
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000

namespace MME.Global45Rate

attribute [local irreducible] D scale component rawProfile rawCount rawDenominator
  coarseAddress marginal
  MME.DWZFourthLogScaleTable.entries MME.DWZFourthRetainedEntropy.entropyRecords
  MME.DWZFourthRetainedEntropy.obligations

local instance boundaryDecidable (c : Fin 45) : Decidable (boundary c) :=
  inferInstanceAs (Decidable (shape c 0 = 0 ∨ shape c 1 = 0))

def prob (c : Fin 45) : ℚ := (component c : ℚ) / scale
def atom (c : Fin 45) (l : Fin 5) : ℚ :=
  prob c * ((rawProfile c).count l : ℚ) / (rawProfile c).denominator

theorem n_eq (t : ℕ) (c : Fin 45) : n t c = component c * (D * t) := by
  apply Nat.mul_div_cancel'
  have hc : (rawProfile c).denominator ∣ D :=
    by
      unfold D
      exact Finset.dvd_prod_of_mem (fun d : Fin 45 => (rawProfile d).denominator)
        (Finset.mem_univ c)
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hc t) (component c)

theorem N_eq (t : ℕ) : N t = scale * (D * t) := by
  simp only [N, n_eq, ← Finset.sum_mul,
    mme_dwz_q5_exact_global_profile_certificate.2.2.1]

theorem D_pos : 0 < D := by
  unfold D
  exact Finset.prod_pos (fun c _ => (rawProfile c).denominator_pos)

theorem N_pos : 0 < N 1 := by
  rw [N_eq, mul_one]
  exact Nat.mul_pos mme_dwz_q5_exact_global_profile_certificate.1 D_pos

theorem occurrence_probability (c : Fin 45) :
    (n 1 c : ℚ) / (N 1 : ℚ) = prob c := by
  rw [n_eq, N_eq, mul_one]
  simp only [Nat.cast_mul, prob]
  have hd : (D : ℚ) ≠ 0 := by exact_mod_cast D_pos.ne'
  field_simp

theorem atom_probability (c : Fin 45) (l : Fin 5) :
    (mu 1 2 c l : ℚ) / (N 1 : ℚ) = atom c l := by
  have hn := occurrence_probability c
  have hden : ((rawProfile c).denominator : ℚ) ≠ 0 := by
    exact_mod_cast (rawProfile c).denominator_pos.ne'
  have hN : (N 1 : ℚ) ≠ 0 := by exact_mod_cast N_pos.ne'
  change ((rawProfile c).denominator * m 1 c : ℕ) / (N 1 : ℚ) = prob c at hn
  push_cast at hn
  change (((rawProfile c).count l * m 1 c : ℕ) : ℚ) / (N 1 : ℚ) = _
  push_cast
  unfold atom
  apply (eq_div_iff hden).2
  rw [← hn]
  ring

noncomputable def fineProb (i : Fin 9 × Fin 5) : ℚ :=
  ∑ c : {c : Fin 45 // coarse c = i.1}, atom c.val i.2

noncomputable def poolProb : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5) → ℚ
  | (Sum.inl c, (g,l)) => if boundary c ∧ coarse c = g then atom c l else 0
  | (Sum.inr g', (g,l)) => if g' = g then fineProb (g,l) -
      ∑ c ∈ Finset.univ.filter (fun c => boundary c ∧ coarse c = g), atom c l
    else 0

theorem fine_probability (i : Fin 9 × Fin 5) :
    (F 1 i : ℚ) / (N 1 : ℚ) = fineProb i := by
  simp only [F, fineProb, Nat.cast_sum, Finset.sum_div, atom_probability]

theorem boundary_sum_le (g : Fin 9) (l : Fin 5) :
    (∑ c ∈ Finset.univ.filter (fun c => boundary c ∧ coarse c = g), mu 1 2 c l) ≤
      F 1 (g,l) := by
  have hsub : (F 1 (g,l)) =
      ∑ c ∈ Finset.univ.filter (fun c => coarse c = g), mu 1 2 c l := by
    unfold F
    exact (Finset.sum_subtype (p := fun c : Fin 45 => coarse c = g)
      (Finset.univ.filter (fun c => coarse c = g)) (by simp)
      (fun c => mu 1 2 c l)).symm
  rw [hsub]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by intro c hc; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *; exact hc.2)
    (by intros; exact Nat.zero_le _)

theorem pool_probability (i : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5)) :
    (pooled 1 i : ℚ) / (N 1 : ℚ) = poolProb i := by
  rcases i with ⟨d,g,l⟩
  cases d with
  | inl c =>
    simp only [pooled, poolProb]
    split_ifs
    · exact atom_probability c l
    · simp
  | inr g' =>
    simp only [pooled, poolProb]
    split_ifs
    · rw [Nat.cast_sub]
      · rw [sub_div, fine_probability]
        simp only [Nat.cast_sum, Finset.sum_div, atom_probability]
        congr 2
        ext c
        simp only [Finset.mem_filter]
      · convert boundary_sum_le g l using 2 <;> congr 1
    · simp

theorem normalized_mass_entropy {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (s : ℝ) (hs : 0 < s)
    (hsum : ∑ i, a i = s) :
    (s * Real.log s - ∑ i, a i * Real.log (a i)) / s =
      ∑ i, Real.negMulLog (a i / s) := by
  have hterm (i : ι) : Real.negMulLog (a i / s) =
      (a i * Real.log s - a i * Real.log (a i)) / s := by
    by_cases hi : a i = 0
    · simp [hi]
    · rw [Real.negMulLog, Real.log_div hi (ne_of_gt hs)]
      ring
  simp only [hterm, ← Finset.sum_div, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hsum]

theorem sum_subtype_ite {C M : Type*} [Fintype C] [AddCommMonoid M]
    (P : C → Prop) [DecidablePred P] [Fintype {c : C // P c}] (f : C → M) :
    (∑ c : {c : C // P c}, f c.val) = ∑ c, if P c then f c else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := P) (F := inferInstance)
    (Finset.univ.filter P) (by simp) f).symm

theorem prob_total : ∑ c, prob c = 1 := by
  simp only [prob, ← Finset.sum_div, ← Nat.cast_sum,
    mme_dwz_q5_exact_global_profile_certificate.2.2.1]
  exact div_self (by exact_mod_cast mme_dwz_q5_exact_global_profile_certificate.1.ne')

theorem atom_total (c : Fin 45) : ∑ l, atom c l = prob c := by
  simp only [atom, ← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum,
    (rawProfile c).count_sum]
  exact mul_div_cancel_right₀ _ (by exact_mod_cast (rawProfile c).denominator_pos.ne')

theorem fineProb_ite (g : Fin 9) (l : Fin 5) :
    fineProb (g,l) = ∑ c : Fin 45, if coarse c = g then atom c l else 0 := by
  exact sum_subtype_ite (fun c : Fin 45 => coarse c = g) (fun c => atom c l)

theorem fineProb_total : ∑ i, fineProb i = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [fineProb_ite]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 5)))
    (t := (Finset.univ : Finset (Fin 45)))]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp [atom_total, prob_total]

noncomputable def rowProb (d : Fin 45 ⊕ Fin 9) : ℚ := ∑ i, poolProb (d,i)
noncomputable def conditional (d : Fin 45 ⊕ Fin 9) (i : Fin 9 × Fin 5) : ℚ :=
  poolProb (d,i) / rowProb d

noncomputable def entropy {ι : Type*} [Fintype ι] (p : ι → ℚ) : ℝ :=
  ∑ i, Real.negMulLog (p i : ℝ)

theorem target_entropy : targetRate = entropy prob := by
  rw [targetRate, normalized_mass_entropy (fun c : Fin 45 => (n 1 c : ℝ))
    (fun c => Nat.cast_nonneg _) (N 1 : ℝ) (by exact_mod_cast N_pos)
    (by simp only [N, Nat.cast_sum])]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  simpa only [Rat.cast_div, Rat.cast_natCast] using
    congrArg (fun q : ℚ => (q : ℝ)) (occurrence_probability c)

theorem F_total : ∑ i, F 1 i = N 1 := by
  have h : (∑ i, (F 1 i : ℚ)) / (N 1 : ℚ) = 1 := by
    simp only [Finset.sum_div, fine_probability, fineProb_total]
  have hN : (N 1 : ℚ) ≠ 0 := by exact_mod_cast N_pos.ne'
  have h' := (div_eq_one_iff_eq hN).mp h
  exact_mod_cast h'

theorem fine_entropy :
    ((N 1 : ℝ) * Real.log (N 1 : ℝ) -
      ∑ i, (F 1 i : ℝ) * Real.log (F 1 i : ℝ)) / (N 1 : ℝ) = entropy fineProb := by
  rw [normalized_mass_entropy (fun i => (F 1 i : ℝ))
    (fun i => Nat.cast_nonneg _) (N 1 : ℝ) (by exact_mod_cast N_pos)
    (by simpa only [Nat.cast_sum] using congrArg (fun n : ℕ => (n : ℝ)) F_total)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simpa only [Rat.cast_div, Rat.cast_natCast] using
    congrArg (fun q : ℚ => (q : ℝ)) (fine_probability i)

theorem conditional_mass_entropy {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (N : ℝ) :
    ((∑ i, a i) * Real.log (∑ i, a i) - ∑ i, a i * Real.log (a i)) / N =
      ((∑ i, a i) / N) * ∑ i, Real.negMulLog (a i / (∑ j, a j)) := by
  by_cases hz : (∑ i, a i) = 0
  · have hz' : ∀ i, a i = 0 := by
      intro i
      exact le_antisymm ((Finset.single_le_sum (fun j _ => ha j)
        (Finset.mem_univ i)).trans_eq hz) (ha i)
    simp [hz']
  · have hp : 0 < ∑ i, a i :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => ha i)) (Ne.symm hz)
    rw [← normalized_mass_entropy a ha _ hp rfl]
    field_simp

theorem conditional_entropy (d : Fin 45 ⊕ Fin 9) :
    ((∑ i, (pooled 1 (d,i) : ℝ)) * Real.log (∑ i, (pooled 1 (d,i) : ℝ)) -
      ∑ i, (pooled 1 (d,i) : ℝ) * Real.log (pooled 1 (d,i) : ℝ)) / (N 1 : ℝ) =
        (rowProb d : ℝ) * entropy (conditional d) := by
  rw [conditional_mass_entropy (fun i => (pooled 1 (d,i) : ℝ))
    (fun i => Nat.cast_nonneg _) (N 1 : ℝ)]
  have hr : (∑ i, (pooled 1 (d,i) : ℝ)) / (N 1 : ℝ) = (rowProb d : ℝ) := by
    simp only [rowProb, Rat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Rat.cast_div, Rat.cast_natCast] using
      congrArg (fun q : ℚ => (q : ℝ)) (pool_probability (d,i))
  rw [hr]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hp : (pooled 1 (d,i) : ℝ) / (N 1 : ℝ) = (poolProb (d,i) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using
      congrArg (fun q : ℚ => (q : ℝ)) (pool_probability (d,i))
  simp only [conditional, Rat.cast_div]
  rw [← hp, ← hr]
  exact (div_div_div_cancel_right₀ (show (N 1 : ℝ) ≠ 0 by exact_mod_cast N_pos.ne') _ _).symm

theorem compatibility_entropy : compatibilityRate = targetRate - entropy fineProb +
    ∑ d, (rowProb d : ℝ) * entropy (conditional d) := by
  rw [← fine_entropy]
  simp_rw [← conditional_entropy]
  simp only [compatibilityRate, targetRate, ← Finset.sum_div,
    Finset.sum_sub_distrib, Fintype.sum_prod_type, Nat.cast_sum]
  ring

noncomputable def listEntropy (xs : List ℚ) : ℝ :=
  (xs.map (fun q : ℚ => Real.negMulLog (q : ℝ))).sum

def recordCells (cells : List ℕ) : List ℚ :=
  cells.filterMap (fun i => (MME.DWZFourthLogScaleTable.entries[i]?).map Prod.fst)

theorem record_entropy_with (tbl : ℕ → Option (ℚ × ℕ)) (cells : List ℕ) :
    entropyActualWith tbl cells =
      listEntropy (cells.filterMap (fun i => (tbl i).map Prod.fst)) := by
  induction cells with
  | nil => rfl
  | cons i is ih =>
    simp only [entropyActualWith, List.filterMap_cons]
    cases he : tbl i with
    | none => simpa using ih
    | some entry =>
      simp only [Option.map_some, List.map_cons, List.sum_cons]
      change Real.negMulLog (entry.1 : ℝ) + _ = Real.negMulLog (entry.1 : ℝ) + _
      exact congrArg (Real.negMulLog (entry.1 : ℝ) + ·) ih

theorem record_entropy (cells : List ℕ) :
    entropyActual cells = listEntropy (recordCells cells) :=
  record_entropy_with (fun i => MME.DWZFourthLogScaleTable.entries[i]?) cells

noncomputable def evalForm (xs : List (ℚ × List ℚ)) : ℝ :=
  (xs.map (fun t : ℚ × List ℚ => (t.1 : ℝ) * listEntropy t.2)).sum

def sourceForm (terms : List MME.DWZFourthRetainedEntropy.EntropyTerm) :
    List (ℚ × List ℚ) :=
  terms.filterMap (fun t => (MME.DWZFourthRetainedEntropy.entropyRecords[t.recordIndex]?).map
    (fun r => (t.coefficient, recordCells r.cells)))

theorem terms_semantics (ts : List MME.DWZFourthRetainedEntropy.EntropyTerm)
    (x : ℝ) (hx : termsActual ts = some x) : evalForm (sourceForm ts) = x := by
  induction ts generalizing x with
  | nil => simpa [termsActual, sourceForm, evalForm] using hx
  | cons t ts ih =>
    simp only [termsActual, termActual, Option.bind_eq_bind] at hx
    cases hr : MME.DWZFourthRetainedEntropy.entropyRecords[t.recordIndex]? with
    | none => simp [hr] at hx
    | some r =>
      cases hrest : termsActual ts with
      | none => simp [hr, hrest] at hx
      | some y =>
        simp only [hr, hrest, Option.bind_some, Option.pure_def, Option.some.injEq] at hx
        rw [← hx]
        simp only [sourceForm, List.filterMap_cons, hr, Option.map_some,
          evalForm, List.map_cons, List.sum_cons]
        rw [record_entropy]
        exact congrArg ((t.coefficient : ℝ) * listEntropy (recordCells r.cells) + ·)
          (ih y hrest)

def canonicalCells (xs : List ℚ) : List ℚ :=
  xs.filter (fun q => q != 0)

theorem listEntropy_filter (xs : List ℚ) :
    listEntropy (xs.filter (fun q => q != 0)) = listEntropy xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x = 0
    · simp [hx, listEntropy] at *; exact ih
    · simp [hx, listEntropy] at *; exact ih

theorem listEntropy_canonical (xs : List ℚ) :
    listEntropy (canonicalCells xs) = listEntropy xs := listEntropy_filter xs


def canonicalForm (xs : List (ℚ × List ℚ)) : List (ℚ × List ℚ) :=
  (xs.filter (fun t => t.1 != 0)).map (fun t => (t.1, canonicalCells t.2))

theorem evalForm_canonical (xs : List (ℚ × List ℚ)) :
    evalForm (canonicalForm xs) = evalForm xs := by
  induction xs with
  | nil => rfl
  | cons t ts ih =>
    by_cases ht : t.1 = 0
    · simpa [canonicalForm, ht, evalForm] using ih
    · simpa [canonicalForm, ht, evalForm, listEntropy_canonical] using
        congrArg ((t.1 : ℝ) * listEntropy t.2 + ·) ih

noncomputable def productList (p : Fin 9 × Fin 5 → ℚ) : List ℚ :=
  (List.ofFn (fun g : Fin 9 => List.ofFn (fun l : Fin 5 => p (g,l)))).flatten

theorem productList_entropy (p : Fin 9 × Fin 5 → ℚ) :
    listEntropy (productList p) = entropy p := by
  simp only [listEntropy, productList, entropy, List.map_flatten, List.sum_flatten,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply, Fintype.sum_prod_type]

noncomputable def compatibilityForm : List (ℚ × List ℚ) :=
  [(1, productList fineProb)] ++
    List.ofFn (fun c : Fin 45 => (-rowProb (Sum.inl c), productList (conditional (Sum.inl c)))) ++
    List.ofFn (fun g : Fin 9 => (-rowProb (Sum.inr g), productList (conditional (Sum.inr g))))

theorem compatibilityForm_semantics : evalForm compatibilityForm =
    entropy fineProb - ∑ d, (rowProb d : ℝ) * entropy (conditional d) := by
  simp only [evalForm, compatibilityForm, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.map_ofFn,
    List.sum_ofFn, Function.comp_apply, Rat.cast_one, Rat.cast_neg, one_mul, add_zero,
    productList_entropy, Fintype.sum_sum_type, neg_mul, Finset.sum_neg_distrib]
  ring

noncomputable def marginalForm (mode : Fin 3) : List (ℚ × List ℚ) :=
  [(1, List.ofFn (fun g : Fin 9 => (marginal mode g : ℚ) / scale)),
    (1, List.ofFn prob)]

theorem marginalForm_semantics (mode : Fin 3) : evalForm (marginalForm mode) =
    marginalEntropy mode + targetRate := by
  rw [target_entropy]
  simp only [marginalForm, evalForm, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Rat.cast_one, one_mul, add_zero,
    listEntropy, List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    marginalEntropy, entropy, Rat.cast_div, Rat.cast_natCast]

theorem branch_lower (i : Fin MME.DWZFourthRetainedEntropy.obligations.size) :
    ((MME.DWZFourthRetainedEntropy.obligations[i]).retainedFloor : ℝ) ≤
      ((MME.DWZFourthRetainedEntropy.obligations[i]).constant : ℝ) +
      evalForm (sourceForm (MME.DWZFourthRetainedEntropy.obligations[i]).terms) := by
  obtain ⟨x, hx, hbound⟩ := mme_dwz_fourth_exact_scalar_certificate.2 i
  rw [terms_semantics _ x hx]
  exact hbound

-- These checks compare exact rational data and cell orderings, without evaluating logarithms.
attribute [local semireducible] scale component rawProfile rawCount rawDenominator
  coarseAddress marginal MME.DWZFourthLogScaleTable.entries
  MME.DWZFourthRetainedEntropy.entropyRecords MME.DWZFourthRetainedEntropy.obligations


-- Exact cached rational distributions, checked against their defining sums.
def fineData (i : Fin 9 × Fin 5) : ℚ :=
  (![![(11728292092203 / 500000000000000 : ℚ), 0, 0, 0, 0], ![(11322757883526924001740354836806432273333694949032964342499 / 200000000000000200000000000000000000000000000000000000000000 : ℚ), (11322757975503098643775504193193567726666305050967035657501 / 200000000000000200000000000000000000000000000000000000000000 : ℚ), 0, 0, 0], ![(8798532139961904347092629382281788860622415034383701106281 / 166666666666666500000000000000000000000000000000000000000000 : ℚ), (61261271415270409739858639637231535084387325050482873736729 / 333333333333333000000000000000000000000000000000000000000000 : ℚ), (17597054202343685110566204060204887194367844880749724050709 / 333333333333333000000000000000000000000000000000000000000000 : ℚ), 0, 0], ![(90916510891217111296650506286519008191250414236430025097 / 19230769230769250000000000000000000000000000000000000000000 : ℚ), (6611648184915424900409663289658881253487439907412934901353 / 38461538461538500000000000000000000000000000000000000000000 : ℚ), (264465544022793165086902292952287041389086912437727689699 / 1538461538461540000000000000000000000000000000000000000000 : ℚ), (90916343275335745311563019230452347701443226585506402989 / 19230769230769250000000000000000000000000000000000000000000 : ℚ), 0], ![(424056194634218804767630374839373609862608779795091443 / 6493506493506500000000000000000000000000000000000000000000 : ℚ), (7636145189331610182340332443491292578264473362346228559229 / 500000000000000500000000000000000000000000000000000000000000 : ℚ), (80056979038239156650589322448043845599501312881325413682803 / 500000000000000500000000000000000000000000000000000000000000 : ℚ), (173548751166231909629620290633610140019335487631306185277 / 11363636363636375000000000000000000000000000000000000000000 : ℚ), (19355262758322282142192606237927619101381994372651787 / 296384113811500000000000000000000000000000000000000000000 : ℚ)], ![0, (244667201806631649948918927239255485692216104464024503216048920390633 / 865800865800865800865800865800000000000000000000000000000000000000000000 : ℚ), (83993135338008165471537390237227954361149531794325044490222113760635723 / 6060606060606060606060606060600000000000000000000000000000000000000000000 : ℚ), (52495700589547490556634826864924566885811718125788814381024606344268633 / 3787878787878787878787878787875000000000000000000000000000000000000000000 : ℚ), (4281679153188721735662650871631498073529016182911702444065434114500083 / 15151515151515151515151515151500000000000000000000000000000000000000000000 : ℚ)], ![0, 0, (113664299509084797119528000536927276917233520446522387 / 537634408602150000000000000000000000000000000000000000000 : ℚ), (19358472966976930622318924285241317682860409086489558711 / 16666666666666650000000000000000000000000000000000000000000 : ℚ), (880898321189520231995709462028484183176337944917061823 / 4166666666666662500000000000000000000000000000000000000000 : ℚ)], ![0, 0, 0, (3235519457396708748426513 / 200000000000000000000000000000 : ℚ), (3235519464603291251573487 / 200000000000000000000000000000 : ℚ)], ![0, 0, 0, 0, (145624853 / 1000000000000000 : ℚ)]]) i.1 i.2

def poolData : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5) → ℚ
  | (Sum.inl c, (g,l)) => if coarse c = g then
      (![![0, 0, 0, 0, (145624853 / 1000000000000000 : ℚ)], ![0, 0, 0, (808879865024021614285377 / 100000000000000000000000000000 : ℚ), (808879865475978385714623 / 100000000000000000000000000000 : ℚ)], ![0, 0, (52851664885010706898305841 / 500000000000000000000000000000 : ℚ), (294852999180729719713597917 / 1000000000000000000000000000000 : ℚ), (105703329774748866489790401 / 1000000000000000000000000000000 : ℚ)], ![0, (17097282782117205393855637 / 133333333333333200000000000000 : ℚ), (37438480475457450963834733 / 16666666666666650000000000000 : ℚ), (299509840484931216130714177 / 133333333333333200000000000000 : ℚ), (17097273978291337552511273 / 133333333333333200000000000000 : ℚ)], ![(6276551996685845645674623 / 200000000000000000000000000000 : ℚ), (1694219407902540785016911781 / 1000000000000000000000000000000 : ℚ), (1185884427714268066269661629 / 125000000000000000000000000000 : ℚ), (1694219907097387346018679783 / 1000000000000000000000000000000 : ℚ), (31382759013498110578742289 / 1000000000000000000000000000000 : ℚ)], ![(13248949136415297900682503 / 125000000000000000000000000000 : ℚ), (2312411217515984276456605503 / 1000000000000000000000000000000 : ℚ), (1156204391553776909724091413 / 500000000000000000000000000000 : ℚ), (105991685170639520889751647 / 1000000000000000000000000000000 : ℚ), 0], ![(34185474297391926846579961 / 400000000000000000000000000000 : ℚ), (334011556481441346815528861 / 1000000000000000000000000000000 : ℚ), (170928815971157672136042473 / 2000000000000000000000000000000 : ℚ), 0, 0], ![(8353230310416341341066407 / 1000000000000000000000000000000 : ℚ), (8353230315083658658933593 / 1000000000000000000000000000000 : ℚ), 0, 0, 0], ![(302564579 / 2000000000000000 : ℚ), 0, 0, 0, 0], ![0, 0, 0, (1617759727348665519855759 / 200000000000000000000000000000 : ℚ), (1617759733651334480144241 / 200000000000000000000000000000 : ℚ)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, (568297463098088944200521 / 5376344086021500000000000000 : ℚ), (191961590135596596633467 / 651041666666666015625000000 : ℚ), (70468885427319051793359371 / 666666666666666000000000000000 : ℚ)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, (51288244292937037477902909 / 400000000000000000000000000000 : ℚ), (898530405850855649298152553 / 400000000000000000000000000000 : ℚ), (898529855157263487446031033 / 400000000000000000000000000000 : ℚ), (10257643569188765155582701 / 80000000000000000000000000000 : ℚ)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(15691393009571762537937063 / 500000000000000000000000000000 : ℚ), (338843935556720720568362367 / 200000000000000000000000000000 : ℚ), (2371768707791101024366417647 / 250000000000000000000000000000 : ℚ), (1694220175694610490629888729 / 1000000000000000000000000000000 : ℚ), (15691392524619141993377361 / 500000000000000000000000000000 : ℚ)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(4080061379843325837854457 / 38461538461538500000000000000 : ℚ), (355741701714590714436347787 / 153846153846154000000000000000 : ℚ), (355741374482151640353416553 / 153846153846154000000000000000 : ℚ), (16320259650885085982399199 / 153846153846154000000000000000 : ℚ), 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(171108017781361205427112537 / 2000000000000000000000000000000 : ℚ), (66766523943924524840525533 / 200000000000000000000000000000 : ℚ), (171106043200393546167632133 / 2000000000000000000000000000000 : ℚ), 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![(16706460592956449547029769 / 2000000000000000000000000000000 : ℚ), (16706460658043550452970231 / 2000000000000000000000000000000 : ℚ), 0, 0, 0], ![0, 0, 0, 0, 0], ![(302564579 / 2000000000000000 : ℚ), 0, 0, 0, 0]]) c l else 0
  | (Sum.inr g', (g,l)) => if g' = g then
      (![![(23456281619827 / 1000000000000000 : ℚ), 0, 0, 0, 0], ![(11319416591405545085176146457127519050417436649032964342499 / 200000000000000200000000000000000000000000000000000000000000 : ℚ), (11319416683374277553657128322672480949582563350967035657501 / 200000000000000200000000000000000000000000000000000000000000 : ℚ), 0, 0, 0], ![(8770029190856210972290577459475192165623443534383701106281 / 166666666666666500000000000000000000000000000000000000000000 : ℚ), (61038656689870055305467312862252858757106167050482873736729 / 333333333333333000000000000000000000000000000000000000000000 : ℚ), (17540048392481759964521401487796756911646945880749724050709 / 333333333333333000000000000000000000000000000000000000000000 : ℚ), 0, 0], ![(1128896344344009077714794988385073590326261 / 250000000000000000000000000000000000000000000 : ℚ), (83639060264570026949913316378296368153717589 / 500000000000000000000000000000000000000000000 : ℚ), (3345557517951476964689128386341690459966087 / 20000000000000000000000000000000000000000000 : ℚ), (1128894119354015388714441993195611583238857 / 250000000000000000000000000000000000000000000 : ℚ), 0], ![(16487714098031687431310611379936569296108779795091443 / 6493506493506500000000000000000000000000000000000000000000 : ℚ), (5941925646488536294191427792419098648902665362346228559229 / 500000000000000500000000000000000000000000000000000000000000 : ℚ), (70569903911799872849702714198769531788019502881325413682803 / 500000000000000500000000000000000000000000000000000000000000 : ℚ), (135043750225413713889976525815452905376511487631306185277 / 11363636363636375000000000000000000000000000000000000000000 : ℚ), (752552603391500479169170038640551674881994372651787 / 296384113811500000000000000000000000000000000000000000000 : ℚ)], ![0, (67897107762176154423616710442200794182851853238828101 / 2597402597402600000000000000000000000000000000000000000000 : ℚ), (170295136138486695302761147563018956679698833658718092831 / 18181818181818200000000000000000000000000000000000000000000 : ℚ), (106434278569436383946009896088181798306894488680967194101 / 11363636363636375000000000000000000000000000000000000000000 : ℚ), (1188214757200497108013021306986901174975053697656499751 / 45454545454545500000000000000000000000000000000000000000000 : ℚ)], ![0, 0, (446959031593546834122182598473418009 / 50000000000000000000000000000000000000000000 : ℚ), (28590118819480530592595389922740531323867 / 50000000000000000000000000000000000000000000 : ℚ), (111739621968965142621973665248814531 / 12500000000000000000000000000000000000000000 : ℚ)], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]) g l else 0

def rowWeight : Fin 45 ⊕ Fin 9 → ℚ := Sum.elim
  (![(145624853 / 1000000000000000 : ℚ), (3235519461 / 200000000000000 : ℚ), (1012519317451 / 2000000000000000 : ℚ), (1899636723147 / 400000000000000 : ℚ), (12938280255711 / 1000000000000000 : ℚ), (9673606557771 / 2000000000000000 : ℚ), (1009879300421 / 2000000000000000 : ℚ), (33412921251 / 2000000000000000 : ℚ), (302564579 / 2000000000000000 : ℚ), (3235519461 / 200000000000000 : ℚ), 0, 0, 0, 0, 0, 0, 0, (1012519317451 / 2000000000000000 : ℚ), 0, 0, 0, 0, 0, 0, (1899636723147 / 400000000000000 : ℚ), 0, 0, 0, 0, 0, (12938280255711 / 1000000000000000 : ℚ), 0, 0, 0, 0, (9673606557771 / 2000000000000000 : ℚ), 0, 0, 0, (1009879300421 / 2000000000000000 : ℚ), 0, 0, (33412921251 / 2000000000000000 : ℚ), 0, (302564579 / 2000000000000000 : ℚ)])
  (![(23456281619827 / 1000000000000000 : ℚ), (113194166373899 / 1000000000000000 : ℚ), (288356290392193 / 1000000000000000 : ℚ), (171793579140753 / 500000000000000 : ℚ), (41228146839217 / 250000000000000 : ℚ), (9392365056437 / 500000000000000 : ℚ), (28591012737 / 50000000000000 : ℚ), 0, 0])

set_option maxHeartbeats 0 in
theorem fine_check : fineProb = fineData := by
  have h : ∀ i, fineProb i = fineData i := by decide +kernel
  exact funext h

set_option maxHeartbeats 0 in
theorem pool_check : poolProb = poolData := by
  funext i
  have h : ∀ i, (match i with
      | (Sum.inl c, (g,l)) => if boundary c ∧ coarse c = g then atom c l else 0
      | (Sum.inr g', (g,l)) => if g' = g then fineData (g,l) -
          ∑ c ∈ Finset.univ.filter (fun c => boundary c ∧ coarse c = g), atom c l
        else 0) = poolData i := by decide +kernel
  unfold poolProb
  rw [fine_check]
  exact h i

set_option maxHeartbeats 0 in
theorem row_check : rowProb = rowWeight := by
  funext d
  unfold rowProb
  rw [pool_check]
  have h : ∀ d, (∑ i, poolData (d,i)) = rowWeight d := by decide +kernel
  exact h d

def sameForm : List (ℚ × List ℚ) → List (ℚ × List ℚ) → Prop
  | [], [] => True
  | a :: as, b :: bs => a.1 = b.1 ∧ a.2.Perm b.2 ∧ sameForm as bs
  | _, _ => False

instance decidableSameForm : (a b : List (ℚ × List ℚ)) → Decidable (sameForm a b)
  | [], [] => isTrue True.intro
  | [], _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)
  | a :: as, b :: bs =>
    haveI : Decidable (sameForm as bs) := decidableSameForm as bs
    inferInstanceAs (Decidable (a.1 = b.1 ∧ a.2.Perm b.2 ∧ sameForm as bs))

theorem evalForm_same {a b : List (ℚ × List ℚ)} (h : sameForm a b) :
    evalForm a = evalForm b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons y ys => exact False.elim h
  | cons x xs ih => cases b with
    | nil => exact False.elim h
    | cons y ys =>
      rcases h with ⟨hcoeff, hperm, htail⟩
      have he : listEntropy x.2 = listEntropy y.2 :=
        (hperm.map (fun q : ℚ => Real.negMulLog (q : ℝ))).sum_eq
      change (x.1 : ℝ) * listEntropy x.2 + evalForm xs =
        (y.1 : ℝ) * listEntropy y.2 + evalForm ys
      rw [hcoeff, he, ih htail]

def fastEntry (i : ℕ) : Option (ℚ × ℕ) :=
  if i < 1920 then (if i < 1856 then (if i < 1792 then (if i < 1728 then (if i < 1664 then (if i < 1600 then (if i < 1536 then (if i < 1472 then (if i < 1408 then (if i < 1344 then (if i < 1280 then (if i < 1216 then (if i < 1152 then (if i < 1088 then (if i < 1024 then (if i < 960 then (if i < 896 then (if i < 832 then (if i < 768 then (if i < 704 then (if i < 640 then (if i < 576 then (if i < 512 then (if i < 448 then (if i < 384 then (if i < 320 then (if i < 256 then (if i < 192 then (if i < 128 then (if i < 64 then (MME.DWZFourthLogScaleTable.chunk0[i]?) else MME.DWZFourthLogScaleTable.chunk1[i-64]?) else MME.DWZFourthLogScaleTable.chunk2[i-128]?) else MME.DWZFourthLogScaleTable.chunk3[i-192]?) else MME.DWZFourthLogScaleTable.chunk4[i-256]?) else MME.DWZFourthLogScaleTable.chunk5[i-320]?) else MME.DWZFourthLogScaleTable.chunk6[i-384]?) else MME.DWZFourthLogScaleTable.chunk7[i-448]?) else MME.DWZFourthLogScaleTable.chunk8[i-512]?) else MME.DWZFourthLogScaleTable.chunk9[i-576]?) else MME.DWZFourthLogScaleTable.chunk10[i-640]?) else MME.DWZFourthLogScaleTable.chunk11[i-704]?) else MME.DWZFourthLogScaleTable.chunk12[i-768]?) else MME.DWZFourthLogScaleTable.chunk13[i-832]?) else MME.DWZFourthLogScaleTable.chunk14[i-896]?) else MME.DWZFourthLogScaleTable.chunk15[i-960]?) else MME.DWZFourthLogScaleTable.chunk16[i-1024]?) else MME.DWZFourthLogScaleTable.chunk17[i-1088]?) else MME.DWZFourthLogScaleTable.chunk18[i-1152]?) else MME.DWZFourthLogScaleTable.chunk19[i-1216]?) else MME.DWZFourthLogScaleTable.chunk20[i-1280]?) else MME.DWZFourthLogScaleTable.chunk21[i-1344]?) else MME.DWZFourthLogScaleTable.chunk22[i-1408]?) else MME.DWZFourthLogScaleTable.chunk23[i-1472]?) else MME.DWZFourthLogScaleTable.chunk24[i-1536]?) else MME.DWZFourthLogScaleTable.chunk25[i-1600]?) else MME.DWZFourthLogScaleTable.chunk26[i-1664]?) else MME.DWZFourthLogScaleTable.chunk27[i-1728]?) else MME.DWZFourthLogScaleTable.chunk28[i-1792]?) else MME.DWZFourthLogScaleTable.chunk29[i-1856]?) else MME.DWZFourthLogScaleTable.chunk30[i-1920]?

theorem entries_lookup (i : ℕ) : MME.DWZFourthLogScaleTable.entries[i]? = fastEntry i := by
  simp only [MME.DWZFourthLogScaleTable.entries, Array.getElem?_append, Array.size_append]
  rfl

theorem sameForm_refl (a : List (ℚ × List ℚ)) : sameForm a a := by
  induction a with
  | nil => trivial
  | cons x xs ih => exact ⟨rfl, List.Perm.refl _, ih⟩

set_option maxHeartbeats 0 in
theorem marginal_zero_form : sameForm (canonicalForm (marginalForm 0)) (canonicalForm
    (sourceForm (MME.DWZFourthRetainedEntropy.obligations[201]'(by decide +kernel)).terms)) := by
  have h : marginalForm 0 = sourceForm (MME.DWZFourthRetainedEntropy.obligations[201]'(by decide +kernel)).terms := by
    simp only [sourceForm, recordCells, entries_lookup]
    decide +kernel
  rw [h]
  exact sameForm_refl _

set_option maxHeartbeats 0 in
theorem marginal_one_form : sameForm (canonicalForm (marginalForm 1)) (canonicalForm
    (sourceForm (MME.DWZFourthRetainedEntropy.obligations[202]'(by decide +kernel)).terms)) := by
  have h : marginalForm 1 = sourceForm (MME.DWZFourthRetainedEntropy.obligations[202]'(by decide +kernel)).terms := by
    simp only [sourceForm, recordCells, entries_lookup]
    decide +kernel
  rw [h]
  exact sameForm_refl _

set_option maxHeartbeats 0 in
theorem compatibility_form : sameForm (canonicalForm compatibilityForm) (canonicalForm
    (sourceForm (MME.DWZFourthRetainedEntropy.obligations[203]'(by decide +kernel)).terms)) := by
  have hc : conditional = (fun d i => poolData (d,i) / rowWeight d) := by
    funext d i
    unfold conditional
    rw [pool_check, row_check]
  simp only [compatibilityForm, hc, fine_check, row_check, sourceForm, recordCells, entries_lookup]
  decide +kernel

theorem evalForm_eq_of_canonical {a b : List (ℚ × List ℚ)}
    (h : sameForm (canonicalForm a) (canonicalForm b)) : evalForm a = evalForm b :=
  (evalForm_canonical a).symm.trans ((evalForm_same h).trans (evalForm_canonical b))

theorem retained_floor : (1490513549769 / 1000000000000 : ℝ) ≤ extractionRate := by
  have h0 := branch_lower ⟨201, by decide +kernel⟩
  have h1 := branch_lower ⟨202, by decide +kernel⟩
  have h2 := branch_lower ⟨203, by decide +kernel⟩
  simp only [Fin.getElem_fin] at h0 h1 h2
  have hc0 : (MME.DWZFourthRetainedEntropy.obligations[201]'(by decide +kernel)).retainedFloor =
      (1490513549769 / 1000000000000 : ℚ) ∧
      (MME.DWZFourthRetainedEntropy.obligations[201]'(by decide +kernel)).constant =
        -entropyUpper := by decide +kernel
  have hc1 : (MME.DWZFourthRetainedEntropy.obligations[202]'(by decide +kernel)).retainedFloor =
      (1490513549769 / 1000000000000 : ℚ) ∧
      (MME.DWZFourthRetainedEntropy.obligations[202]'(by decide +kernel)).constant =
        -entropyUpper := by decide +kernel
  have hc2 : (MME.DWZFourthRetainedEntropy.obligations[203]'(by decide +kernel)).retainedFloor =
      (1490513549769 / 1000000000000 : ℚ) ∧
      (MME.DWZFourthRetainedEntropy.obligations[203]'(by decide +kernel)).constant = 0 :=
    by decide +kernel
  rw [hc0.1, hc0.2, ← evalForm_eq_of_canonical marginal_zero_form,
    marginalForm_semantics] at h0
  rw [hc1.1, hc1.2, ← evalForm_eq_of_canonical marginal_one_form,
    marginalForm_semantics] at h1
  rw [hc2.1, hc2.2, ← evalForm_eq_of_canonical compatibility_form,
    compatibilityForm_semantics] at h2
  push_cast at h0 h1 h2
  have hT := mme_dwz_q5_coarse_entropy_lower_bounds.1
  have hC := compatibility_entropy
  have hmax : hashRate ≤ targetRate - (1490513549769 / 1000000000000 : ℝ) := by
    unfold hashRate
    apply max_le
    · linarith
    · apply max_le
      · linarith
      · apply max_le
        · linarith
        · linarith
  unfold extractionRate
  linarith

end MME.Global45Rate

theorem solution : (14905135 / 10000000 : ℝ) < MME.DWZQ5AsymptoticData.extractionRate := by
  have h := MME.Global45Rate.retained_floor
  linarith
