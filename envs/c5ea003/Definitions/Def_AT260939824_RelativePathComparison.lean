-- Prove2me | Definitions.Def_AT260939824_RelativePathComparison
-- name    : AT260939824_RelativePathComparison
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:49:13.611247+00:00
-- url     : https://prove2.me/theorems/a36c4fed-c7ac-45d2-80f0-c90875c27a3d
-- title:
--   Uniform comparison estimates for relative contraction homotopies
-- statement:
--   Let $H$ be a contraction of a metric space to a fixed point $p$, fixing $p$, with track bound $D$ and joint bound $J$. Let $P:p\to q$ be $S$-Lipschitz and let $P':p\to q'$ be another path. The four-stage endpoint-preserving homotopy satisfies
--   $$d\bigl(\mathcal R_H(P)(s,u),\mathcal R_H(P')(s',u)\bigr)
--   \le24(1+J)\bigl(E+(S+D)|s-s'|\bigr)$$
--   whenever $d(P(u),P'(u))\le E$ for all $u\in I$, with $E\ge0$. The corresponding uniform-metric estimate replaces $E$ by $\sup_u d(P(u),P'(u))$. In particular the homotopy-parameter bound is $24(1+J)(S+D)$, and comparison at equal parameters has bound $(1+J)E$. The endpoint $q'$ may differ from $q$.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RelativePathComparison.lean, selected declaration lines 10-30, 32-58, 60-64, 66-76, 83-88, 90-95, 97-102, 104-106, 108-117, 119-130, 132-152, 154-190, 192-197, 199-231, 233-250, 252-261; SHA-256 eb85643227bd6772bd6f0ae6e61dc03b1a9107f264153d5bc9e8b0e5ad643318. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_RelativePathBounds
import Definitions.Def_AT260939824_RelativePathContraction
import Init
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

namespace AbelianTargets

open scoped unitInterval NNReal

noncomputable section

theorem quotient_lipschitz_of_width (a : I → ℝ)
    (ha : ∀ s, (1/3 : ℝ) ≤ a s) (hla : LipschitzWith (2/3) a)
    (v : ℝ) (hv : |v| ≤ 1) : LipschitzWith 6 (fun s => v/a s) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have has : 0 < a s := lt_of_lt_of_le (by norm_num) (ha s)
  have hat : 0 < a t := lt_of_lt_of_le (by norm_num) (ha t)
  have hab : (1/9 : ℝ) ≤ a s*a t := by nlinarith [ha s,ha t]
  have hd := hla.dist_le_mul s t
  change |a s-a t| ≤ (2/3 : ℝ)*dist s t at hd
  have hn : |v| * |a t-a s| ≤ (2/3 : ℝ)*dist s t := by
    calc |v| * |a t-a s| ≤ |a t-a s| := mul_le_of_le_one_left (abs_nonneg _) hv
         _ = |a s-a t| := abs_sub_comm _ _
         _ ≤ _ := hd
  have hbig : (2/3 : ℝ)*dist s t ≤ 6*dist s t*(a s*a t) := by
    have hh := mul_le_mul_of_nonneg_left hab (show 0 ≤ 6*dist s t by positivity)
    nlinarith
  change |v/a s-v/a t| ≤ (6 : ℝ)*dist s t
  rw [show v/a s-v/a t = v*(a t-a s)/(a s*a t) by field_simp,
    abs_div, abs_mul, abs_of_pos (mul_pos has hat)]
  exact (div_le_iff₀ (mul_pos has hat)).mpr (hn.trans hbig)

theorem homotopy_trans_parameter_lipschitz {Z : Type*} [MetricSpace Z]
    {p q : Z} {P Q R : Path p q} {K : ℝ≥0} (F : P.Homotopy Q) (G : Q.Homotopy R)
    (hF : ∀ u, LipschitzWith K (fun s : I => F (s,u)))
    (hG : ∀ u, LipschitzWith K (fun s : I => G (s,u))) :
    ∀ u, LipschitzWith (2*K) (fun s : I => (F.trans G) (s,u)) := by
  intro u
  have hleft : LipschitzWith (2*K) (fun s : ℝ => F (clampInterval (2*s),u)) := by
    have hh := (hF u).comp (lipschitz_clampInterval.comp (lipschitz_affine_le 2 2 0 (by norm_num)))
    simpa [Function.comp_def, mul_comm] using hh
  have hright : LipschitzWith (2*K) (fun s : ℝ => G (clampInterval (2*s-1),u)) := by
    have hh := (hG u).comp (lipschitz_clampInterval.comp (lipschitz_affine_le 2 2 (-1) (by norm_num)))
    simpa [Function.comp_def, sub_eq_add_neg, mul_comm] using hh
  have hfull := lipschitz_glue_at _ _ hleft hright (1/2)
    (show F (clampInterval (2*(1/2)),u) = G (clampInterval (2*(1/2)-1),u) by norm_num)
  have hres := hfull.comp (LipschitzWith.subtype_val (Set.Icc (0 : ℝ) 1))
  have heq : (fun s : I => if (s : ℝ) ≤ 1/2 then F (clampInterval (2*s),u)
      else G (clampInterval (2*s-1),u)) = (fun s : I => (F.trans G) (s,u)) := by
    funext s
    rw [Path.Homotopy.trans_apply]
    split_ifs with hs
    · rw [show clampInterval (2*(s : ℝ)) = ⟨2*(s : ℝ),
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.property.1,hs⟩⟩ from
        Set.projIcc_of_mem zero_le_one ((unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.property.1,hs⟩)]
    · rw [show clampInterval (2*(s : ℝ)-1) = ⟨2*(s : ℝ)-1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.mp hs).le,s.property.2⟩⟩ from
        Set.projIcc_of_mem zero_le_one (unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.mp hs).le,s.property.2⟩)]
  simpa only [Function.comp_def, mul_one, heq] using hres

theorem lipschitz_interval_symm : LipschitzWith 1 unitInterval.symm := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change |(1-(s : ℝ))-(1-(t : ℝ))| ≤ (1 : ℝ)*|(s : ℝ)-(t : ℝ)|
  rw [one_mul, show (1-(s : ℝ))-(1-(t : ℝ)) = -((s : ℝ)-(t : ℝ)) by ring, abs_neg]

theorem homotopy_trans_dist_le {Z : Type*} [MetricSpace Z]
    {p q p' q' : Z} {P Q R : Path p q} {P' Q' R' : Path p' q'}
    (F : P.Homotopy Q) (G : Q.Homotopy R) (F' : P'.Homotopy Q') (G' : Q'.Homotopy R')
    (B : ℝ) (hF : ∀ s u, dist (F (s,u)) (F' (s,u)) ≤ B)
    (hG : ∀ s u, dist (G (s,u)) (G' (s,u)) ≤ B) :
    ∀ s u, dist ((F.trans G) (s,u)) ((F'.trans G') (s,u)) ≤ B := by
  intro s u
  rw [Path.Homotopy.trans_apply, Path.Homotopy.trans_apply]
  split_ifs
  · exact hF _ u
  · exact hG _ u

namespace ControlledContraction

variable {Z : Type*} [MetricSpace Z] {p q : Z} {D J S : ℝ≥0}
variable (H : ControlledContraction p D J)

theorem compressionWidth_lipschitz : LipschitzWith (2/3) compressionWidth := by
  have hh := (lipschitz_affine_le (2/3) (-2/3) 1 (by norm_num)).comp
    (LipschitzWith.subtype_val (Set.Icc (0 : ℝ) 1))
  have heq : (fun s : I => (-2/3 : ℝ)*(s : ℝ)+1) = compressionWidth := by
    funext s; unfold compressionWidth; ring
  simpa only [Function.comp_def, mul_one, heq] using hh

theorem expansionWidth_lipschitz : LipschitzWith (2/3) expansionWidth := by
  have hh := (lipschitz_affine_le (2/3) (2/3) (1/3) (by norm_num)).comp
    (LipschitzWith.subtype_val (Set.Icc (0 : ℝ) 1))
  have heq : (fun s : I => (2/3 : ℝ)*(s : ℝ)+1/3) = expansionWidth := by
    funext s; unfold expansionWidth pauseWidth; ring
  simpa only [Function.comp_def, mul_one, heq] using hh

theorem compressRaw_parameter_lipschitz (P : Path p q) (hP : LipschitzWith S P) (u : I) :
    LipschitzWith (6*S) (fun s : I => compressRaw P (s,(u : ℝ))) := by
  have hu : |(u : ℝ)| ≤ 1 := by rw [abs_of_nonneg u.property.1]; exact u.property.2
  have hh := hP.comp (lipschitz_clampInterval.comp
    (quotient_lipschitz_of_width compressionWidth compressionWidth_ge compressionWidth_lipschitz u hu))
  simpa only [Function.comp_def, compressRaw, one_mul, mul_comm] using hh

theorem fixed_time_lipschitz (t : I) : LipschitzWith J (fun z : Z => H.map (z,t)) := by
  have hh := H.joint.comp ((LipschitzWith.id).prodMk (LipschitzWith.const t))
  simpa only [Function.comp_def, max_zero, mul_one] using hh

theorem spurRaw_parameter_lipschitz (P : Path p q) (u : I) :
    LipschitzWith D (fun s : I => H.spurRaw P (s,(u : ℝ))) := by
  unfold spurRaw slot3
  dsimp only
  split_ifs
  · exact (LipschitzWith.const (α := I) (P (clampInterval (3*(u : ℝ))))).weaken bot_le
  · simpa only [Function.comp_def, mul_one, mul_comm] using
      (H.track q).comp (lipschitz_interval_mul (clampInterval (3*(u : ℝ)-1)))
  · simpa only [Function.comp_def, mul_one, mul_comm] using
      (H.track q).comp (lipschitz_interval_mul (clampInterval (3-3*(u : ℝ))))

theorem thirdRaw_parameter_lipschitz (P : Path p q) (hP : LipschitzWith S P) (u : I) :
    LipschitzWith ((1+J)*S) (fun r : I => H.thirdRaw P (r,(u : ℝ))) := by
  unfold thirdRaw slot3
  dsimp only
  split_ifs
  · have hh : LipschitzWith S (fun r : I => P (r*clampInterval (3*(u : ℝ)))) := by
      simpa only [Function.comp_def, mul_one, mul_comm] using
        hP.comp (lipschitz_interval_mul (clampInterval (3*(u : ℝ))))
    exact hh.weaken (by rw [add_mul,one_mul]; exact le_add_of_nonneg_right bot_le)
  · have hh := (H.fixed_time_lipschitz (clampInterval (3*(u : ℝ)-1))).comp hP
    exact hh.weaken (by rw [add_mul,one_mul]; exact le_add_of_nonneg_left bot_le)
  · exact (LipschitzWith.const (α := I) (H.map (q,clampInterval (3-3*(u : ℝ))))).weaken bot_le

theorem expandRaw_parameter_lipschitz (q : Z) (u : I) :
    LipschitzWith (6*D) (fun s : I => H.expandRaw q (s,(u : ℝ))) := by
  have hu : |(u : ℝ)-1| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr u.property.2)]
    have := u.property.1
    linarith
  have hquot := quotient_lipschitz_of_width expansionWidth expansionWidth_ge
    expansionWidth_lipschitz ((u : ℝ)-1) hu
  have harg : LipschitzWith 6 (fun s : I => 1+((u : ℝ)-1)/expansionWidth s) := by
    simpa only [Function.comp_def, one_mul, add_comm] using
      (lipschitz_affine_le 1 1 1 (by norm_num)).comp hquot
  have heq : (fun s : I => ((u : ℝ)-pauseWidth s)/expansionWidth s) =
      (fun s : I => 1+((u : ℝ)-1)/expansionWidth s) := by
    funext s
    have h0 := ne_of_gt (expansionWidth_pos s)
    apply (div_eq_iff h0).mpr
    field_simp
    unfold expansionWidth
    ring
  have hh := (H.shortPath_lipschitz q).comp (lipschitz_clampInterval.comp (heq ▸ harg))
  simpa only [Function.comp_def, expandRaw, one_mul, mul_comm] using hh

theorem relativeHomotopy_parameter_lipschitz (P : Path p q) (hP : LipschitzWith S P) :
    ∀ u, LipschitzWith (24*(1+J)*(S+D)) (fun s : I => H.relativeHomotopy P (s,u)) := by
  let K : ℝ≥0 := 6*(1+J)*(S+D)
  have hS : 6*S ≤ K := by
    have hh : S ≤ (1+J)*(S+D) := by
      calc S ≤ S+D := le_add_of_nonneg_right bot_le
           _ ≤ (1+J)*(S+D) := by rw [add_mul,one_mul]; exact le_add_of_nonneg_right bot_le
    simpa only [K,mul_assoc] using mul_le_mul_of_nonneg_left hh (show (0 : ℝ≥0) ≤ 6 by norm_num)
  have hD : 6*D ≤ K := by
    have hh : D ≤ (1+J)*(S+D) := by
      calc D ≤ S+D := le_add_of_nonneg_left bot_le
           _ ≤ (1+J)*(S+D) := by rw [add_mul,one_mul]; exact le_add_of_nonneg_right bot_le
    simpa only [K,mul_assoc] using mul_le_mul_of_nonneg_left hh (show (0 : ℝ≥0) ≤ 6 by norm_num)
  have hDS : D ≤ K := (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (show (1 : ℝ≥0) ≤ 6 by norm_num) (show 0 ≤ D from bot_le) : D ≤ 6*D).trans hD
  have hJS : (1+J)*S ≤ K := by
    calc (1+J)*S ≤ (1+J)*(S+D) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right bot_le) bot_le
         _ ≤ 6*((1+J)*(S+D)) := by
           simpa only [one_mul] using mul_le_mul_of_nonneg_right (show (1 : ℝ≥0) ≤ 6 by norm_num) (show 0 ≤ (1+J)*(S+D) from bot_le)
         _ = K := by dsimp [K]; ring
  have h₁ : ∀ u, LipschitzWith K (fun s : I => compressionHomotopy P (s,u)) :=
    fun u => (compressRaw_parameter_lipschitz P hP u).weaken hS
  have h₂ : ∀ u, LipschitzWith K (fun s : I => H.spurHomotopy P (s,u)) :=
    fun u => (H.spurRaw_parameter_lipschitz P u).weaken hDS
  have h₃ : ∀ u, LipschitzWith K (fun s : I => H.thirdHomotopy P (s,u)) := by
    intro u
    simpa only [Function.comp_def, mul_one] using
      ((H.thirdRaw_parameter_lipschitz P hP u).comp lipschitz_interval_symm).weaken (by simpa only [mul_one] using hJS)
  have h₄ : ∀ u, LipschitzWith K (fun s : I => H.expansionHomotopy q (s,u)) :=
    fun u => (H.expandRaw_parameter_lipschitz q u).weaken hD
  have hh := homotopy_trans_parameter_lipschitz
    ((compressionHomotopy P).trans (H.spurHomotopy P))
    ((H.thirdHomotopy P).trans (H.expansionHomotopy q))
    (homotopy_trans_parameter_lipschitz _ _ h₁ h₂)
    (homotopy_trans_parameter_lipschitz _ _ h₃ h₄)
  have hK : 2*(2*K) = 24*(1+J)*(S+D) := by dsimp [K]; ring
  simpa only [relativeHomotopy, hK] using hh

theorem map_fixed_time_dist_le {z z' : Z} (t : I) (E : ℝ≥0)
    (hzz : dist z z' ≤ E) : dist (H.map (z,t)) (H.map (z',t)) ≤ (1+(J : ℝ))*E := by
  calc dist (H.map (z,t)) (H.map (z',t)) ≤ (J : ℝ)*dist z z' :=
         (H.fixed_time_lipschitz t).dist_le_mul z z'
       _ ≤ (J : ℝ)*E := mul_le_mul_of_nonneg_left hzz J.property
       _ ≤ (1+(J : ℝ))*E := by rw [add_mul,one_mul]; exact le_add_of_nonneg_left E.property

/-- Uniform comparison of different input paths, including different
terminal points. This is the input-path term of Equation (3). -/
theorem relativeHomotopy_input_dist_le {q' : Z} (P : Path p q) (P' : Path p q')
    (E : ℝ≥0) (hPP : ∀ u, dist (P u) (P' u) ≤ E) :
    ∀ s u, dist (H.relativeHomotopy P (s,u)) (H.relativeHomotopy P' (s,u)) ≤ (1+(J : ℝ))*E := by
  have hE : (E : ℝ) ≤ (1+(J : ℝ))*E := by
    rw [add_mul,one_mul]
    exact le_add_of_nonneg_right (mul_nonneg J.property E.property)
  have hqq : dist q q' ≤ E := by simpa only [Path.target] using hPP 1
  have h₁ : ∀ s u, dist (compressionHomotopy P (s,u)) (compressionHomotopy P' (s,u)) ≤ (1+(J : ℝ))*E := by
    intro s u
    exact (hPP (clampInterval ((u : ℝ)/compressionWidth s))).trans hE
  have h₂ : ∀ s u, dist (H.spurHomotopy P (s,u)) (H.spurHomotopy P' (s,u)) ≤ (1+(J : ℝ))*E := by
    intro s u
    change dist (H.spurRaw P (s,(u : ℝ))) (H.spurRaw P' (s,(u : ℝ))) ≤ _
    unfold spurRaw slot3
    split_ifs
    · exact (hPP _).trans hE
    · exact H.map_fixed_time_dist_le _ E hqq
    · exact H.map_fixed_time_dist_le _ E hqq
  have h₃ : ∀ s u, dist (H.thirdHomotopy P (s,u)) (H.thirdHomotopy P' (s,u)) ≤ (1+(J : ℝ))*E := by
    intro s u
    change dist (H.thirdRaw P (unitInterval.symm s,(u : ℝ))) (H.thirdRaw P' (unitInterval.symm s,(u : ℝ))) ≤ _
    unfold thirdRaw slot3
    split_ifs
    · exact (hPP _).trans hE
    · exact H.map_fixed_time_dist_le _ E (hPP _)
    · exact H.map_fixed_time_dist_le _ E hqq
  have h₄ : ∀ s u, dist (H.expansionHomotopy q (s,u)) (H.expansionHomotopy q' (s,u)) ≤ (1+(J : ℝ))*E := by
    intro s u
    exact H.map_fixed_time_dist_le _ E hqq
  exact homotopy_trans_dist_le _ _ _ _ _
    (homotopy_trans_dist_le _ _ _ _ _ h₁ h₂) (homotopy_trans_dist_le _ _ _ _ _ h₃ h₄)

/-- Equation (3), pointwise, with the explicit absolute constant 24. -/
theorem relativeHomotopy_comparison {q' : Z} (P : Path p q) (P' : Path p q')
    (hP : LipschitzWith S P) (E : ℝ≥0) (hPP : ∀ u, dist (P u) (P' u) ≤ E)
    (s s' u : I) :
    dist (H.relativeHomotopy P (s,u)) (H.relativeHomotopy P' (s',u)) ≤
      24*(1+(J : ℝ))*((E : ℝ)+((S : ℝ)+D)*dist s s') := by
  have hp := (H.relativeHomotopy_parameter_lipschitz P hP u).dist_le_mul s s'
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_one] at hp
  have hi := H.relativeHomotopy_input_dist_le P P' E hPP s' u
  calc
    _ ≤ dist (H.relativeHomotopy P (s,u)) (H.relativeHomotopy P (s',u)) +
      dist (H.relativeHomotopy P (s',u)) (H.relativeHomotopy P' (s',u)) := dist_triangle _ _ _
    _ ≤ 24*(1+(J : ℝ))*((S : ℝ)+D)*dist s s' + (1+(J : ℝ))*E := add_le_add hp hi
    _ ≤ 24*(1+(J : ℝ))*((S : ℝ)+D)*dist s s' + 24*((1+(J : ℝ))*E) := by
      apply add_le_add le_rfl
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (show (1 : ℝ) ≤ 24 by norm_num) (mul_nonneg (by positivity : 0 ≤ 1+(J : ℝ)) E.property)
    _ = _ := by ring

/-- Literal uniform-metric form of Equation (3). The input uniform
distance is the usual metric on continuous maps from the compact interval. -/
theorem relativeHomotopy_uniform_comparison {q' : Z} (P : Path p q) (P' : Path p q')
    (hP : LipschitzWith S P) (s s' : I) :
    dist ((H.relativeHomotopy P).eval s).toContinuousMap ((H.relativeHomotopy P').eval s').toContinuousMap ≤
      24*(1+(J : ℝ))*(dist P.toContinuousMap P'.toContinuousMap+((S : ℝ)+D)*dist s s') := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro u
  exact H.relativeHomotopy_comparison P P' hP
    (nndist P.toContinuousMap P'.toContinuousMap) (fun u => ContinuousMap.dist_apply_le_dist u) s s' u

end ControlledContraction
end
end AbelianTargets


