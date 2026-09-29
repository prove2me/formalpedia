-- Prove2me | solution 1 for Erdos183.exists_recursivePaletteStage
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:24:41.51279+00:00
-- url     : https://prove2.me/submissions/0388a30d-69be-4cdd-94b7-84d6e02c6204

import Definitions.Def_erdos183_core
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Data.Int.Star
import Theorems.Thm_Erdos183_cliqueFree_pullback_embedding
import Theorems.Thm_Erdos183_factorial_exp_lower
import Theorems.Thm_Erdos183_labelGraph_pullback_embedding

open Filter Finset SimpleGraph
open scoped Topology

namespace Erdos183

theorem colorable_pullback_embedding {U V K : Type*} {j : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V K)
    (f : U ↪ V) (colour : K)
    (hC : (C.labelGraph colour).Colorable j) :
    ((C.pullback f).labelGraph colour).Colorable j := by
  obtain ⟨label⟩ := hC
  refine ⟨SimpleGraph.Coloring.mk (fun u => label (f u)) ?_⟩
  intro u v hadj
  apply label.valid
  rw [labelGraph_pullback_embedding] at hadj
  exact hadj

theorem no_three_pairwise_palette_disagreements {α : Type*}
    (P Q R : Finset α) (colour : α)
    (hPQ : (colour ∈ P) ≠ (colour ∈ Q))
    (hQR : (colour ∈ Q) ≠ (colour ∈ R))
    (hRP : (colour ∈ R) ≠ (colour ∈ P)) : False := by
  classical
  by_cases hP : colour ∈ P <;>
    by_cases hQ : colour ∈ Q <;>
      by_cases hR : colour ∈ R <;>
        simp_all

theorem paletteSeparated_insert {α : Type*} [DecidableEq α]
    {s : ℕ} {family : Finset (Finset α)} {P : Finset α}
    (hseparated : IsPaletteSeparated s family)
    (hequal : ∀ Q ∈ family, Q.card = P.card)
    (hfar : ∀ Q ∈ family, s ≤ (P \ Q).card) :
    IsPaletteSeparated s (insert P family) := by
  classical
  intro X hX Y hY hXY
  by_cases hXP : X = P
  · subst X
    by_cases hYP : Y = P
    · exact (hXY hYP.symm).elim
    · have hYfamily : Y ∈ family :=
        (Finset.mem_insert.mp hY).resolve_left hYP
      exact hfar Y hYfamily
  · have hXfamily : X ∈ family :=
      (Finset.mem_insert.mp hX).resolve_left hXP
    by_cases hYP : Y = P
    · subst Y
      rw [Finset.card_sdiff_comm (hequal X hXfamily)]
      exact hfar X hXfamily
    · have hYfamily : Y ∈ family :=
        (Finset.mem_insert.mp hY).resolve_left hYP
      exact hseparated X hXfamily Y hYfamily hXY

theorem exists_maximal_separated_palette_cover {α : Type*} [DecidableEq α]
    (ambient : Finset (Finset α)) (s : ℕ) (hs : 0 < s)
    (hequal : ∀ P ∈ ambient, ∀ Q ∈ ambient, P.card = Q.card) :
    ∃ family : Finset (Finset α),
      family ⊆ ambient ∧ IsPaletteSeparated s family ∧
        ∀ P ∈ ambient, ∃ Q ∈ family, (P \ Q).card < s := by
  classical
  let candidates := ambient.powerset.filter (IsPaletteSeparated s)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, IsPaletteSeparated]
  obtain ⟨family, hfamily, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card hcandidates
  have hfamily' : family ⊆ ambient ∧ IsPaletteSeparated s family := by
    simpa [candidates] using hfamily
  refine ⟨family, hfamily'.1, hfamily'.2, ?_⟩
  intro P hP
  by_contra hnot
  have hfar : ∀ Q ∈ family, s ≤ (P \ Q).card := by
    intro Q hQ
    exact Nat.le_of_not_gt (fun hclose => hnot ⟨Q, hQ, hclose⟩)
  have hPnot : P ∉ family := by
    intro hPF
    apply hnot
    refine ⟨P, hPF, ?_⟩
    simpa using hs
  have hcards : ∀ Q ∈ family, Q.card = P.card := by
    intro Q hQ
    exact hequal Q (hfamily'.1 hQ) P hP
  have hinsert_separated : IsPaletteSeparated s (insert P family) :=
    paletteSeparated_insert hfamily'.2 hcards hfar
  have hinsert : insert P family ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.insert_subset hP hfamily'.1, hinsert_separated⟩
  have hmaxcard := hmax (insert P family) hinsert
  rw [Finset.card_insert_of_notMem hPnot] at hmaxcard
  omega

theorem paletteShell_card_le (N t d : ℕ)
    (Q : Finset (Fin N)) (hQ : Q.card = t) :
    (paletteShell N t Q d).card ≤
      t.choose d * (N - t).choose d := by
  classical
  have hcard := Fintype.card_le_of_injective
    (paletteShellEmbedding N t d Q hQ)
    (paletteShellEmbedding N t d Q hQ).injective
  calc
    (paletteShell N t Q d).card = Fintype.card ↥(paletteShell N t Q d) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card
      (↥(Q.powersetCard d) ×
        ↥(((Finset.univ : Finset (Fin N)) \ Q).powersetCard d)) := hcard
    _ = t.choose d * (N - t).choose d := by
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
        Finset.card_powersetCard, Finset.card_powersetCard,
        Finset.card_sdiff_of_subset (Finset.subset_univ Q)]
      simp [hQ]

theorem palette_packing_card_le {α : Type*} [DecidableEq α]
    (ambient family : Finset (Finset α)) (s ballBound : ℕ)
    (hcover : ∀ P ∈ ambient, ∃ Q ∈ family, (P \ Q).card < s)
    (hball : ∀ Q ∈ family, (paletteBall ambient Q s).card ≤ ballBound) :
    ambient.card ≤ family.card * ballBound := by
  classical
  have hsubset : ambient ⊆ family.biUnion (fun Q => paletteBall ambient Q s) := by
    intro P hP
    obtain ⟨Q, hQ, hclose⟩ := hcover P hP
    exact Finset.mem_biUnion.mpr ⟨Q, hQ, by simp [paletteBall, hP, hclose]⟩
  calc
    ambient.card ≤ (family.biUnion (fun Q => paletteBall ambient Q s)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ Q ∈ family, (paletteBall ambient Q s).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _Q ∈ family, ballBound :=
      Finset.sum_le_sum fun Q hQ => hball Q hQ
    _ = family.card * ballBound := by simp

theorem paletteBall_card_le_binomial_sum (N t s : ℕ)
    (Q : Finset (Fin N)) (hQ : Q.card = t) :
    (paletteBall ((Finset.univ : Finset (Fin N)).powersetCard t) Q s).card ≤
      ∑ d ∈ Finset.range s, t.choose d * (N - t).choose d := by
  classical
  let ambient : Finset (Finset (Fin N)) :=
    (Finset.univ : Finset (Fin N)).powersetCard t
  have hsubset :
      paletteBall ambient Q s ⊆
        (Finset.range s).biUnion (fun d => paletteShell N t Q d) := by
    intro P hP
    have hP' : P ∈ ambient ∧ (P \ Q).card < s := by
      simpa [paletteBall] using hP
    apply Finset.mem_biUnion.mpr
    refine ⟨(P \ Q).card, Finset.mem_range.mpr hP'.2, ?_⟩
    simpa [paletteShell, ambient] using hP'.1
  calc
    (paletteBall ambient Q s).card ≤
        ((Finset.range s).biUnion (fun d => paletteShell N t Q d)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ d ∈ Finset.range s, (paletteShell N t Q d).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ d ∈ Finset.range s, t.choose d * (N - t).choose d := by
      exact Finset.sum_le_sum fun d _ => paletteShell_card_le N t d Q hQ

theorem exists_separated_palette_packing (N t s : ℕ) (hs : 0 < s) :
    ∃ family : Finset (Finset (Fin N)),
      family ⊆ (Finset.univ : Finset (Fin N)).powersetCard t ∧
      IsPaletteSeparated s family ∧
      N.choose t ≤ family.card *
        (∑ d ∈ Finset.range s, t.choose d * (N - t).choose d) := by
  classical
  obtain ⟨family, hfamily, hseparated, hcover⟩ :=
    exists_maximal_separated_palette_cover
      ((Finset.univ : Finset (Fin N)).powersetCard t) s hs
      (fun P hP Q hQ => (Finset.mem_powersetCard.mp hP).2.trans
        (Finset.mem_powersetCard.mp hQ).2.symm)
  refine ⟨family, hfamily, hseparated, ?_⟩
  have hpacking := palette_packing_card_le
    ((Finset.univ : Finset (Fin N)).powersetCard t) family s
    (∑ d ∈ Finset.range s, t.choose d * (N - t).choose d)
    hcover (fun Q hQ => paletteBall_card_le_binomial_sum N t s Q
      (Finset.mem_powersetCard.mp (hfamily hQ)).2)
  simpa using hpacking

theorem stage_palette_numerator_bound (j t : ℕ) :
    j ^ t ≤ (j * t).choose t := by
  have hcard := Fintype.card_le_of_injective
    (transversalPaletteEmbedding j t)
    (transversalPaletteEmbedding j t).injective
  calc
    j ^ t = Fintype.card (Fin t → Fin j) := by simp
    _ ≤ Fintype.card
      ↥((Finset.univ : Finset (Fin (j * t))).powersetCard t) := hcard
    _ = (j * t).choose t := by
      rw [Fintype.card_coe, Finset.card_powersetCard]
      simp

theorem choose_le_choose_of_le_half {N d s : ℕ}
    (hds : d ≤ s) (hhalf : 2 * s ≤ N) :
    N.choose d ≤ N.choose s := by
  induction hds with
  | refl => exact le_rfl
  | @step d hds ih =>
      have hprevious : 2 * d ≤ N := by omega
      exact (ih hprevious).trans
        (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem choose_le_exp_mul_div_pow (N s : ℕ) (hs : 0 < s) :
    (N.choose s : ℝ) ≤
      (Real.exp 1 * (N : ℝ) / (s : ℝ)) ^ s := by
  have hsreal : 0 < (s : ℝ) := by exact_mod_cast hs
  have hsmall : 0 < ((s : ℝ) / Real.exp 1) ^ s := by positivity
  calc
    (N.choose s : ℝ) ≤ (N : ℝ) ^ s / (s.factorial : ℝ) :=
      Nat.choose_le_pow_div s N
    _ ≤ (N : ℝ) ^ s / (((s : ℝ) / Real.exp 1) ^ s) :=
      div_le_div_of_nonneg_left (by positivity) hsmall
        (factorial_exp_lower s hs)
    _ = (Real.exp 1 * (N : ℝ) / (s : ℝ)) ^ s := by
      rw [← div_pow]
      congr 1
      field_simp

theorem palette_binomial_sum_le (N t s : ℕ)
    (hhalf : 2 * s ≤ t) (htN : t ≤ N) :
    (∑ d ∈ Finset.range s,
      t.choose d * (N - t).choose d) ≤
        s * t.choose s * N.choose s := by
  have hNhalf : 2 * s ≤ N := hhalf.trans htN
  calc
    (∑ d ∈ Finset.range s,
      t.choose d * (N - t).choose d) ≤
        ∑ _d ∈ Finset.range s, t.choose s * N.choose s := by
      apply Finset.sum_le_sum
      intro d hd
      have hds : d ≤ s := by
        have := Finset.mem_range.mp hd
        omega
      apply Nat.mul_le_mul
      · exact choose_le_choose_of_le_half hds hhalf
      · exact (Nat.choose_le_choose d (Nat.sub_le N t)).trans
          (choose_le_choose_of_le_half hds hNhalf)
    _ = s * t.choose s * N.choose s := by simp [mul_assoc]

theorem exists_stage_palette_packing_binomial (j t s : ℕ)
    (hs : 0 < s) (hj : 0 < j) (hhalf : 2 * s ≤ t) :
    ∃ family : Finset (Finset (Fin (j * t))),
      family ⊆ (Finset.univ : Finset (Fin (j * t))).powersetCard t ∧
      IsPaletteSeparated s family ∧
      j ^ t ≤ family.card *
        (s * t.choose s * (j * t).choose s) := by
  obtain ⟨family, hfamily, hseparated, hpacking⟩ :=
    exists_separated_palette_packing (j * t) t s hs
  refine ⟨family, hfamily, hseparated,
    (stage_palette_numerator_bound j t).trans (hpacking.trans ?_)⟩
  exact Nat.mul_le_mul_left _
    (palette_binomial_sum_le (j * t) t s hhalf
      (Nat.le_mul_of_pos_left t hj))

theorem exists_stage_palette_packing_exp (j a s : ℕ)
    (hj : 0 < j) (ha : 2 ≤ a) (hs : 0 < s) :
    ∃ family : Finset (Finset (Fin (j * (a * s)))),
      family ⊆
        (Finset.univ : Finset (Fin (j * (a * s)))).powersetCard (a * s) ∧
      IsPaletteSeparated s family ∧
      (j : ℝ) ^ (a * s) ≤
        (family.card : ℝ) * (s : ℝ) *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ)) ^ s := by
  have hhalf : 2 * s ≤ a * s := Nat.mul_le_mul_right s ha
  obtain ⟨family, hfamily, hseparated, hpacking⟩ :=
    exists_stage_palette_packing_binomial j (a * s) s hs hj hhalf
  refine ⟨family, hfamily, hseparated, ?_⟩
  have hreal :
      (j : ℝ) ^ (a * s) ≤
        (family.card : ℝ) *
          ((s * (a * s).choose s * (j * (a * s)).choose s : ℕ) : ℝ) := by
    exact_mod_cast hpacking
  have hfirst := choose_le_exp_mul_div_pow (a * s) s hs
  have hsecond := choose_le_exp_mul_div_pow (j * (a * s)) s hs
  have hbase :
      (Real.exp 1 * ((a * s : ℕ) : ℝ) / (s : ℝ)) *
        (Real.exp 1 * ((j * (a * s) : ℕ) : ℝ) / (s : ℝ)) =
          Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ) := by
    push_cast
    field_simp
  have hpowers :
      (Real.exp 1 * ((a * s : ℕ) : ℝ) / (s : ℝ)) ^ s *
        (Real.exp 1 * ((j * (a * s) : ℕ) : ℝ) / (s : ℝ)) ^ s =
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ)) ^ s := by
    rw [← mul_pow, hbase]
  calc
    (j : ℝ) ^ (a * s) ≤
        (family.card : ℝ) *
          ((s * (a * s).choose s * (j * (a * s)).choose s : ℕ) : ℝ) :=
      hreal
    _ = (family.card : ℝ) * (s : ℝ) *
          ((a * s).choose s : ℝ) *
          ((j * (a * s)).choose s : ℝ) := by
      push_cast
      ring
    _ ≤ (family.card : ℝ) * (s : ℝ) *
          (Real.exp 1 * ((a * s : ℕ) : ℝ) / (s : ℝ)) ^ s *
          (Real.exp 1 * ((j * (a * s) : ℕ) : ℝ) / (s : ℝ)) ^ s := by
      gcongr
    _ = (family.card : ℝ) * (s : ℝ) *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ)) ^ s := by
      calc
        (family.card : ℝ) * (s : ℝ) *
            (Real.exp 1 * ((a * s : ℕ) : ℝ) / (s : ℝ)) ^ s *
            (Real.exp 1 * ((j * (a * s) : ℕ) : ℝ) / (s : ℝ)) ^ s =
          (family.card : ℝ) * (s : ℝ) *
            ((Real.exp 1 * ((a * s : ℕ) : ℝ) / (s : ℝ)) ^ s *
              (Real.exp 1 * ((j * (a * s) : ℕ) : ℝ) / (s : ℝ)) ^ s) := by
                ring
        _ = (family.card : ℝ) * (s : ℝ) *
            (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ)) ^ s := by
              rw [hpowers]

namespace PaletteBlockCertificate

theorem noMonochromaticTriangle {I V K : Type*} [DecidableEq K]
    {C : SimpleGraph.TopEdgeLabeling (I × V) K} {j : ℕ}
    (certificate : PaletteBlockCertificate C j) :
    ∀ colour : K, (C.labelGraph colour).CliqueFree 3 := by
  classical
  intro colour t ht
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ :=
    (SimpleGraph.is3Clique_iff).mp ht
  rcases x with ⟨i, u⟩
  rcases y with ⟨i', v⟩
  rcases z with ⟨i'', w⟩
  by_cases hii' : i = i'
  · subst i'
    by_cases hii'' : i = i''
    · subst i''
      exact certificate.internal_no_triangle i colour u v w ⟨hxy, hxz, hyz⟩
    · by_cases hmissing : colour ∈ certificate.palette i
      · exact certificate.missing_has_no_internal_edge i colour hmissing u v hxy
      · have hequal := certificate.cross_edges_force_equal_active_labels
          i i'' colour u v w hii'' hmissing hxz hyz
        exact certificate.internal_labels_proper
          i colour hmissing u v hxy hequal
  · by_cases hii'' : i = i''
    · subst i''
      by_cases hmissing : colour ∈ certificate.palette i
      · exact certificate.missing_has_no_internal_edge i colour hmissing u w hxz
      · have hequal := certificate.cross_edges_force_equal_active_labels
          i i' colour u w v hii' hmissing hxy hyz.symm
        exact certificate.internal_labels_proper
          i colour hmissing u w hxz hequal
    · by_cases hi'i'' : i' = i''
      · subst i''
        by_cases hmissing : colour ∈ certificate.palette i'
        · exact certificate.missing_has_no_internal_edge
            i' colour hmissing v w hyz
        · have hequal := certificate.cross_edges_force_equal_active_labels
            i' i colour v w u (Ne.symm hii') hmissing hxy.symm hxz.symm
          exact certificate.internal_labels_proper
            i' colour hmissing v w hyz hequal
      · exact no_three_pairwise_palette_disagreements
          (certificate.palette i) (certificate.palette i')
          (certificate.palette i'') colour
          (certificate.cross_edge_changes_membership
            i i' colour u v hii' hxy)
          (certificate.cross_edge_changes_membership
            i' i'' colour v w hi'i'' hyz)
          (certificate.cross_edge_changes_membership
            i'' i colour w u (Ne.symm hii'') hxz.symm)

theorem colourGraph_colorable {I V K : Type*} [DecidableEq K]
    {C : SimpleGraph.TopEdgeLabeling (I × V) K} {j : ℕ}
    (certificate : PaletteBlockCertificate C j) (colour : K) :
    (C.labelGraph colour).Colorable (j + 1) := by
  classical
  refine ⟨SimpleGraph.Coloring.mk (globalLabel certificate colour) ?_⟩
  intro x y hadj
  rcases x with ⟨i, u⟩
  rcases y with ⟨i', v⟩
  by_cases hs : i = i'
  · subst i'
    by_cases hmissing : colour ∈ certificate.palette i
    · exact False.elim
        (certificate.missing_has_no_internal_edge i colour hmissing u v hadj)
    · have hproper := certificate.internal_labels_proper
        i colour hmissing u v hadj
      simp only [globalLabel, dif_neg hmissing]
      exact fun heq => hproper (Fin.castSucc_inj.mp heq)
  · have hchange := certificate.cross_edge_changes_membership
      i i' colour u v hs hadj
    by_cases hi : colour ∈ certificate.palette i
    · have hi' : colour ∉ certificate.palette i' := by
        intro h
        exact hchange (propext ⟨fun _ => h, fun _ => hi⟩)
      simp only [globalLabel, dif_pos hi, dif_neg hi']
      exact Ne.symm (Fin.castSucc_ne_last _)
    · have hi' : colour ∈ certificate.palette i' := by
        by_contra h
        exact hchange (propext ⟨fun h' => (hi h').elim, fun h' => (h h').elim⟩)
      simp only [globalLabel, dif_neg hi, dif_pos hi']
      exact Fin.castSucc_ne_last _


end PaletteBlockCertificate

theorem mem_missingSymbolRows (H m : ℕ)
    (T : Finset (Fin m → Fin H)) (symbol : Fin H)
    (row : (Fin m → Fin H) → Fin H) :
    row ∈ missingSymbolRows H m T symbol ↔
      ∀ column ∈ T, row column ≠ symbol := by
  classical
  rw [missingSymbolRows, Fintype.mem_piFinset]
  constructor
  · intro hrow column hcolumn
    simpa [hcolumn] using hrow column
  · intro hrow column
    by_cases hcolumn : column ∈ T
    · simpa [hcolumn] using hrow column hcolumn
    · simp [hcolumn]

theorem card_missingSymbolRows (H m : ℕ)
    (T : Finset (Fin m → Fin H)) (symbol : Fin H) :
    (missingSymbolRows H m T symbol).card =
      (H - 1) ^ T.card * H ^ (H ^ m - T.card) := by
  classical
  calc
    (missingSymbolRows H m T symbol).card =
        ∏ column : Fin m → Fin H,
          if column ∈ T then H - 1 else H := by
      rw [missingSymbolRows, Fintype.card_piFinset]
      apply Finset.prod_congr rfl
      intro column _
      split_ifs <;> simp
    _ = (H - 1) ^ T.card * H ^ (H ^ m - T.card) := by
      rw [Finset.prod_ite]
      simp [Finset.filter_notMem_eq_sdiff, Finset.card_sdiff_of_subset]

theorem card_badSaturationRows_le (H m : ℕ)
    (T : Finset (Fin m → Fin H)) :
    (badSaturationRows H m T).card ≤
      H * ((H - 1) ^ T.card * H ^ (H ^ m - T.card)) := by
  classical
  have hsubset : badSaturationRows H m T ⊆
      (Finset.univ : Finset (Fin H)).biUnion
        (fun symbol => missingSymbolRows H m T symbol) := by
    intro row hrow
    have hbad : ¬ RowCovers T row := by
      simpa [badSaturationRows] using hrow
    unfold RowCovers at hbad
    push Not at hbad
    obtain ⟨symbol, hsymbol⟩ := hbad
    exact Finset.mem_biUnion.mpr
      ⟨symbol, Finset.mem_univ symbol,
        (mem_missingSymbolRows H m T symbol row).mpr hsymbol⟩
  calc
    (badSaturationRows H m T).card ≤
        ((Finset.univ : Finset (Fin H)).biUnion
          (fun symbol => missingSymbolRows H m T symbol)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ symbol : Fin H, (missingSymbolRows H m T symbol).card :=
      Finset.card_biUnion_le
    _ = H * ((H - 1) ^ T.card * H ^ (H ^ m - T.card)) := by
      simp [card_missingSymbolRows]

theorem missing_symbol_power_bound (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ)) :
    (H : ℝ) ^ 2 * ((H : ℝ) - 1) ^ (m + 1) <
      (H : ℝ) ^ (m + 1) := by
  have hHpos : 0 < (H : ℝ) := by
    exact_mod_cast (show 0 < H by omega)
  have hfrac_nonneg : 0 ≤ 1 - 1 / (H : ℝ) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hHpos).mpr
    norm_num
    exact_mod_cast (show 1 ≤ H by omega)
  have hfrac_exp : 1 - 1 / (H : ℝ) ≤
      Real.exp (-(1 / (H : ℝ))) := by
    linarith [Real.add_one_le_exp (-(1 / (H : ℝ)))]
  have hfrac_strict :
      (1 - 1 / (H : ℝ)) ^ (m + 1) < ((H : ℝ) ^ 2)⁻¹ := by
    calc
      (1 - 1 / (H : ℝ)) ^ (m + 1) ≤
          Real.exp (-(1 / (H : ℝ))) ^ (m + 1) :=
        pow_le_pow_left₀ hfrac_nonneg hfrac_exp _
      _ = Real.exp (-((m + 1 : ℕ) : ℝ) / (H : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ < Real.exp (-2 * Real.log (H : ℝ)) := by
        apply Real.exp_strictMono
        apply (div_lt_iff₀ hHpos).mpr
        push_cast
        nlinarith
      _ = ((H : ℝ) ^ 2)⁻¹ := by
        rw [show -2 * Real.log (H : ℝ) =
          -(Real.log (H : ℝ) + Real.log (H : ℝ)) by ring]
        rw [Real.exp_neg, Real.exp_add, Real.exp_log hHpos, ← pow_two]
  have hidentity : 1 - 1 / (H : ℝ) = ((H : ℝ) - 1) / H := by
    field_simp
  rw [hidentity, div_pow] at hfrac_strict
  have hcross := (div_lt_div_iff₀
    (pow_pos hHpos (m + 1)) (pow_pos hHpos 2)).mp
      (show ((H : ℝ) - 1) ^ (m + 1) / (H : ℝ) ^ (m + 1) <
        1 / (H : ℝ) ^ 2 by simpa [one_div] using hfrac_strict)
  simpa [mul_comm] using hcross

theorem missing_symbol_power_bound_nat (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ)) :
    H ^ 2 * (H - 1) ^ (m + 1) < H ^ (m + 1) := by
  have hreal := missing_symbol_power_bound H m hH hm
  have hcast :
      ((H ^ 2 * (H - 1) ^ (m + 1) : ℕ) : ℝ) <
        ((H ^ (m + 1) : ℕ) : ℝ) := by
    simpa [Nat.cast_sub (show 1 ≤ H by omega)] using hreal
  exact_mod_cast hcast

theorem card_badSaturationRows_mul_lt (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ))
    (T : Finset (Fin m → Fin H)) (hT : T.card = m + 1) :
    (badSaturationRows H m T).card * H < H ^ (H ^ m) := by
  have hcolumns : m + 1 ≤ H ^ m := by
    calc
      m + 1 = T.card := hT.symm
      _ ≤ Fintype.card (Fin m → Fin H) := Finset.card_le_univ T
      _ = H ^ m := by simp
  have hremaining : 0 < H ^ (H ^ m - (m + 1)) := by
    exact pow_pos (show 0 < H by omega) _
  calc
    (badSaturationRows H m T).card * H ≤
        (H * ((H - 1) ^ T.card * H ^ (H ^ m - T.card))) * H :=
      Nat.mul_le_mul_right H (card_badSaturationRows_le H m T)
    _ = (H ^ 2 * (H - 1) ^ (m + 1)) *
          H ^ (H ^ m - (m + 1)) := by rw [hT]; ring
    _ < H ^ (m + 1) * H ^ (H ^ m - (m + 1)) :=
      Nat.mul_lt_mul_of_pos_right
        (missing_symbol_power_bound_nat H m hH hm) hremaining
    _ = H ^ (H ^ m) := by
      rw [← pow_add]
      congr 1
      omega

theorem card_badSaturationRows_lt_pow (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ))
    (T : Finset (Fin m → Fin H)) (hT : T.card = m + 1) :
    (badSaturationRows H m T).card < H ^ (H ^ m - 1) := by
  have hpositive : 0 < H ^ m := pow_pos (show 0 < H by omega) _
  have hpower : H ^ (H ^ m) = H ^ (H ^ m - 1) * H := by
    rw [← pow_succ]
    congr 1
    omega
  have hrows := card_badSaturationRows_mul_lt H m hH hm T hT
  rw [hpower] at hrows
  exact (Nat.mul_lt_mul_right (show 0 < H by omega)).mp hrows

theorem card_badSaturationMatrices (H m s : ℕ)
    (T : Finset (Fin m → Fin H)) :
    (badSaturationMatrices H m s T).card =
      (badSaturationRows H m T).card ^ s := by
  classical
  simp [badSaturationMatrices, Fintype.card_piFinset]

theorem exists_saturated_of_bad_row_union_bound (H m s : ℕ)
    (hbound :
      (∑ T ∈
          (Finset.univ : Finset (Fin m → Fin H)).powersetCard (m + 1),
        (badSaturationRows H m T).card ^ s) <
          Fintype.card (Fin s → (Fin m → Fin H) → Fin H)) :
    ∃ A : Fin s → (Fin m → Fin H) → Fin H, IsSaturated A := by
  classical
  by_contra hno
  push Not at hno
  let columnSets : Finset (Finset (Fin m → Fin H)) :=
    (Finset.univ : Finset (Fin m → Fin H)).powersetCard (m + 1)
  have hcover :
      (Finset.univ : Finset (Fin s → (Fin m → Fin H) → Fin H)) ⊆
        columnSets.biUnion (fun T => badSaturationMatrices H m s T) := by
    intro A _
    have hA := hno A
    unfold IsSaturated at hA
    push Not at hA
    obtain ⟨T, hTcard, hrows⟩ := hA
    apply Finset.mem_biUnion.mpr
    refine ⟨T, ?_, ?_⟩
    · simp [columnSets, hTcard]
    · simp only [badSaturationMatrices, Fintype.mem_piFinset,
        badSaturationRows, Finset.mem_filter, Finset.mem_univ, true_and]
      intro row
      unfold RowCovers
      intro hcover_row
      obtain ⟨symbol, hmissing⟩ := hrows row
      obtain ⟨column, hcolumn, heq⟩ := hcover_row symbol
      exact hmissing column hcolumn heq
  have hcard :
      Fintype.card (Fin s → (Fin m → Fin H) → Fin H) ≤
        ∑ T ∈ columnSets, (badSaturationMatrices H m s T).card := by
    calc
      Fintype.card (Fin s → (Fin m → Fin H) → Fin H) =
          (Finset.univ : Finset (Fin s → (Fin m → Fin H) → Fin H)).card := by
            simp
      _ ≤ (columnSets.biUnion
        (fun T => badSaturationMatrices H m s T)).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ T ∈ columnSets, (badSaturationMatrices H m s T).card :=
        Finset.card_biUnion_le
  simp_rw [card_badSaturationMatrices] at hcard
  change
    Fintype.card (Fin s → (Fin m → Fin H) → Fin H) ≤
      ∑ T ∈
        (Finset.univ : Finset (Fin m → Fin H)).powersetCard (m + 1),
          (badSaturationRows H m T).card ^ s at hcard
  exact (Nat.not_lt_of_ge hcard) hbound

theorem exists_saturated_matrix (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ)) :
    ∃ A : Fin (m * (m + 1) + 1) → (Fin m → Fin H) → Fin H,
      IsSaturated A := by
  classical
  let s := m * (m + 1) + 1
  let columnSets : Finset (Finset (Fin m → Fin H)) :=
    (Finset.univ : Finset (Fin m → Fin H)).powersetCard (m + 1)
  apply exists_saturated_of_bad_row_union_bound H m s
  have hterms : ∀ T ∈ columnSets,
      (badSaturationRows H m T).card ^ s ≤
        (H ^ (H ^ m - 1)) ^ s := by
    intro T hT
    have hcard : T.card = m + 1 :=
      (Finset.mem_powersetCard.mp hT).2
    exact Nat.pow_le_pow_left
      (card_badSaturationRows_lt_pow H m hH hm T hcard).le s
  have hnumber : columnSets.card ≤ (H ^ m) ^ (m + 1) := by
    dsimp [columnSets]
    simpa using Nat.choose_le_pow (H ^ m) (m + 1)
  have hpositive : 0 < H ^ m := pow_pos (show 0 < H by omega) _
  change
    (∑ T ∈ columnSets, (badSaturationRows H m T).card ^ s) <
      Fintype.card (Fin s → (Fin m → Fin H) → Fin H)
  calc
    (∑ T ∈ columnSets, (badSaturationRows H m T).card ^ s) ≤
        columnSets.card * (H ^ (H ^ m - 1)) ^ s := by
      calc
        (∑ T ∈ columnSets, (badSaturationRows H m T).card ^ s) ≤
            ∑ _T ∈ columnSets, (H ^ (H ^ m - 1)) ^ s := by
          exact Finset.sum_le_sum fun T hT => hterms T hT
        _ = columnSets.card * (H ^ (H ^ m - 1)) ^ s := by simp
    _ ≤ (H ^ m) ^ (m + 1) * (H ^ (H ^ m - 1)) ^ s :=
      Nat.mul_le_mul_right _ hnumber
    _ = H ^ (m * (m + 1) + (H ^ m - 1) * s) := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
    _ < H ^ (H ^ m * s) := by
      apply Nat.pow_lt_pow_right (show 1 < H by omega)
      calc
        m * (m + 1) + (H ^ m - 1) * s <
            s + (H ^ m - 1) * s := by
          apply Nat.add_lt_add_right
          dsimp [s]
          omega
        _ = 1 * s + (H ^ m - 1) * s := by simp
        _ = (1 + (H ^ m - 1)) * s := by rw [Nat.add_mul]
        _ = H ^ m * s := by
          congr 1
          omega
    _ = Fintype.card (Fin s → (Fin m → Fin H) → Fin H) := by
      simp [← pow_mul]

theorem exists_saturated_matrix_ceil (H : ℕ) (hH : 2 ≤ H) :
    ∃ A : Fin (saturatedMatrixRows H) →
        (Fin (saturatedMatrixWidth H) → Fin H) → Fin H,
      IsSaturated A := by
  have hwidth :
      2 * (H : ℝ) * Real.log (H : ℝ) ≤
        (saturatedMatrixWidth H : ℝ) := by
    exact Nat.le_ceil _
  simpa [saturatedMatrixRows] using
    exists_saturated_matrix H (saturatedMatrixWidth H) hH hwidth

theorem saturated_coordinate_covering {H m s : ℕ}
    (A : Fin s → (Fin m → Fin H) → Fin H)
    (hA : IsSaturated A) (hH : 0 < H) (hms : m ≤ s) :
    ∃ f g : (Fin s → Fin H) → (Fin s → Fin H),
      ∀ x y : Fin s → Fin H,
        (∃ row : Fin s, x row = f y row) ∨
        (∃ row : Fin s, y row = g x row) := by
  classical
  refine ⟨forwardGuess A hA hH hms, backwardGuess A hms, ?_⟩
  intro x y
  by_cases hback : ∃ row : Fin s, y row = backwardGuess A hms x row
  · exact Or.inr hback
  · left
    let z : Fin m → Fin H := fun coordinate => x (Fin.castLE hms coordinate)
    have hz : z ∈ exceptionalColumns A y := by
      apply (mem_exceptionalColumns A y z).mpr
      intro row heq
      apply hback
      refine ⟨row, ?_⟩
      simpa [backwardGuess, z] using heq.symm
    let ez : exceptionalColumns A y := ⟨z, hz⟩
    let index := exceptionalColumnIndex A hA y
    let row : Fin s := Fin.castLE hms (index ez)
    refine ⟨row, ?_⟩
    have hexists : ∃ w : exceptionalColumns A y,
        Fin.castLE hms (index w) = row := ⟨ez, rfl⟩
    have hindex : index (Classical.choose hexists) = index ez :=
      Fin.castLE_injective hms (Classical.choose_spec hexists)
    have hchosen : Classical.choose hexists = ez := index.injective hindex
    change x row =
      if h : ∃ w : exceptionalColumns A y,
          Fin.castLE hms (index w) = row then
        (Classical.choose h).val (index (Classical.choose h))
      else
        ⟨0, hH⟩
    rw [dif_pos hexists, hchosen]

theorem exists_coordinate_covering (H : ℕ) (hH : 2 ≤ H) :
    ∃ f g : (Fin (saturatedMatrixRows H) → Fin H) →
        (Fin (saturatedMatrixRows H) → Fin H),
      IsCoordinateCovering f g := by
  obtain ⟨A, hA⟩ := exists_saturated_matrix_ceil H hH
  have hwidth : saturatedMatrixWidth H ≤ saturatedMatrixRows H := by
    dsimp [saturatedMatrixRows]
    nlinarith [sq_nonneg (saturatedMatrixWidth H : ℤ)]
  exact saturated_coordinate_covering A hA (by omega) hwidth

theorem exists_recursivePaletteColouring_fin
    {n N t j H : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin (N - t)))
    (htriangle : ∀ colour : Fin (N - t),
      (C.labelGraph colour).CliqueFree 3)
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hH : 2 ≤ H) (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated (saturatedMatrixRows H) family) :
    ∃ C' : SimpleGraph.TopEdgeLabeling
        (Fin (family.card * n)) (Fin N),
      TriangleFree C' ∧
        (∀ colour : Fin N, (C'.labelGraph colour).Colorable (j + 1)) := by
  classical
  obtain ⟨f, g, hcover⟩ := exists_coordinate_covering H hH
  let C' := recursivePaletteColouring C hC hj family hcard hseparated
    f g hcover
  let certificate := recursivePaletteCertificate C htriangle hC hj family
    hcard hseparated f g hcover
  have hproduct : Fintype.card (↥family × Fin n) = family.card * n := by
    simp
  let embedding : Fin (family.card * n) ↪ (↥family × Fin n) :=
    (Fintype.equivFinOfCardEq hproduct).symm.toEmbedding
  refine ⟨C'.pullback embedding, ?_, ?_⟩
  · exact cliqueFree_pullback_embedding C' embedding
      certificate.noMonochromaticTriangle
  · intro colour
    exact colorable_pullback_embedding C' embedding colour
      (certificate.colourGraph_colorable colour)

theorem paletteGrowthBound_succ {a s j n B : ℕ}
    (hstage : ((j + 1 : ℕ) : ℝ) ^ (a * s) ≤
      (B : ℝ) * (s : ℝ) *
        (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * ((j + 1 : ℕ) : ℝ)) ^ s)
    (hprevious : PaletteGrowthBound a s j n) :
    PaletteGrowthBound a s (j + 1) (B * n) := by
  unfold PaletteGrowthBound at hprevious ⊢
  calc
    (((j + 1).factorial : ℕ) : ℝ) ^ (a * s) =
        ((j + 1 : ℕ) : ℝ) ^ (a * s) *
          (j.factorial : ℝ) ^ (a * s) := by
      simp [Nat.factorial_succ, mul_pow]
    _ ≤
        ((B : ℝ) * (s : ℝ) *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 *
            ((j + 1 : ℕ) : ℝ)) ^ s) *
        ((n : ℝ) * (s : ℝ) ^ j *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * j) *
          (j.factorial : ℝ) ^ s) := by
      exact mul_le_mul hstage hprevious (by positivity) (by positivity)
    _ =
        ((B * n : ℕ) : ℝ) * (s : ℝ) ^ (j + 1) *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * (j + 1)) *
          (((j + 1).factorial : ℕ) : ℝ) ^ s := by
      push_cast
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.mul_succ, pow_add, pow_succ, mul_pow]
      ring

end Erdos183

open Erdos183

theorem solution (H a j : ℕ)
    (hH : 2 ≤ H) (ha : 2 ≤ a) (hj : j ≤ H) :
    ∃ (n : ℕ)
      (C : SimpleGraph.TopEdgeLabeling (Fin n)
        (Fin (j * (a * saturatedMatrixRows H)))),
      TriangleFree C ∧
        (∀ colour : Fin (j * (a * saturatedMatrixRows H)),
          (C.labelGraph colour).Colorable (j + 1)) ∧
        PaletteGrowthBound a (saturatedMatrixRows H) j n := by
  classical
  have hs : 0 < saturatedMatrixRows H := by
    simp [saturatedMatrixRows]
  induction j with
  | zero =>
      refine ⟨1, (by simpa using singletonZeroColouring), ?_, ?_, ?_⟩
      · intro colour
        exact Fin.elim0 (by simpa using colour)
      · intro colour
        exact Fin.elim0 (by simpa using colour)
      · simp [PaletteGrowthBound]
  | succ j ih =>
      obtain ⟨n, C, htriangle, hcolour, hgrowth⟩ := ih (by omega)
      obtain ⟨family, hfamily, hseparated, hstage⟩ :=
        exists_stage_palette_packing_exp (j + 1) a
          (saturatedMatrixRows H) (by omega) ha hs
      have hcard :
          ∀ P ∈ family, P.card = a * saturatedMatrixRows H := by
        intro P hP
        exact (Finset.mem_powersetCard.mp (hfamily hP)).2
      have hsubtract :
          (j + 1) * (a * saturatedMatrixRows H) -
            a * saturatedMatrixRows H =
              j * (a * saturatedMatrixRows H) := by
        simp [Nat.succ_mul]
      have hstep := @exists_recursivePaletteColouring_fin
        n ((j + 1) * (a * saturatedMatrixRows H))
        (a * saturatedMatrixRows H) (j + 1) H
      rw [hsubtract] at hstep
      obtain ⟨C', htriangle', hcolour'⟩ :=
        hstep C htriangle hcolour hH hj family hcard hseparated
      exact ⟨family.card * n, C', htriangle', hcolour',
        paletteGrowthBound_succ hstage hgrowth⟩
