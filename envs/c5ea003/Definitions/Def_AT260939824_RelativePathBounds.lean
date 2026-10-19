-- Prove2me | Definitions.Def_AT260939824_RelativePathBounds
-- name    : AT260939824_RelativePathBounds
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:44:05.130688+00:00
-- url     : https://prove2.me/theorems/fb6696f3-0306-47b9-9675-2661b89eab23
-- title:
--   Path-time bounds for the endpoint-preserving contraction homotopy
-- statement:
--   Let $Z$ be a metric space, $p\in Z$, and let $H:Z\times I\to Z$ be a basepoint-fixing contraction to $p$, with time-track bound $D\ge0$ and joint bound $J\ge0$. For an $S$-Lipschitz path $P:p\to q$, the four-stage relative homotopy $\mathcal R_H(P)$ deforms $P$ to $t\mapsto H(q,1-t)$ while fixing both endpoints. Its selected path-time bound is
--   $$\operatorname{Lip}\bigl(u\mapsto\mathcal R_H(P)(s,u)\bigr)\le3\max\{S,D\}\qquad(s\in I).$$
--   The bundle includes affine rescaling, clamping, and gluing estimates used to bound all four stages. The displayed constant depends on path speed and contraction track speed, with no dependence on the joint constant $J$.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RelativePathBounds.lean, selected declaration lines 10-17, 19-41, 43-50, 52-58, 60-80, 87-95, 97-99, 101-107, 109-114, 116-124, 126-134, 136-144, 146-160, 162-185; SHA-256 5ab61c116b63b791be4e8808895df1a123a8223113b64961e793cdae57d7444d. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_RelativePathContraction
import Init
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

namespace AbelianTargets

open scoped NNReal unitInterval

noncomputable section

theorem lipschitz_affine_le (K : ℝ≥0) (c b : ℝ) (hc : |c| ≤ K) :
    LipschitzWith K (fun x : ℝ => c*x+b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (c*x+b) (c*y+b) = |c*(x-y)| := by rw [Real.dist_eq]; congr 1; ring
    _ = |c| * dist x y := by rw [abs_mul, Real.dist_eq]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc dist_nonneg

theorem lipschitz_glue_at {Z : Type*} [PseudoMetricSpace Z] {K : ℝ≥0}
    (f g : ℝ → Z) (hf : LipschitzWith K f) (hg : LipschitzWith K g)
    (c : ℝ) (hmatch : f c = g c) :
    LipschitzWith K (fun x => if x ≤ c then f x else g x) := by
  have hcross : ∀ x y, x ≤ c → c ≤ y → dist (f x) (g y) ≤ K * dist x y := by
    intro x y hx hy
    calc
      dist (f x) (g y) ≤ dist (f x) (f c) + dist (f c) (g y) := dist_triangle _ _ _
      _ = dist (f x) (f c) + dist (g c) (g y) := by rw [hmatch]
      _ ≤ (K : ℝ)*dist x c + K*dist c y := add_le_add (hf.dist_le_mul x c) (hg.dist_le_mul c y)
      _ = K*dist x y := by
        simp only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx),
          abs_of_nonpos (sub_nonpos.mpr hy), abs_of_nonpos (sub_nonpos.mpr (hx.trans hy))]
        ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x ≤ c <;> by_cases hy : y ≤ c
  · simp only [if_pos hx, if_pos hy]; exact hf.dist_le_mul x y
  · simp only [if_pos hx, if_neg hy]; exact hcross x y hx (le_of_lt (lt_of_not_ge hy))
  · simp only [if_neg hx, if_pos hy]
    rw [dist_comm, dist_comm x y]
    exact hcross y x hy (le_of_lt (lt_of_not_ge hx))
  · simp only [if_neg hx, if_neg hy]; exact hg.dist_le_mul x y

theorem lipschitz_slot3 {Z : Type*} [PseudoMetricSpace Z] {K : ℝ≥0}
    (f g h : ℝ → Z) (hf : LipschitzWith K f) (hg : LipschitzWith K g) (hh : LipschitzWith K h)
    (hfg : f (1/3) = g (1/3)) (hgh : g (2/3) = h (2/3)) :
    LipschitzWith K (fun u => if u ≤ (1/3 : ℝ) then f u else if u ≤ (2/3 : ℝ) then g u else h u) := by
  apply lipschitz_glue_at f (fun u => if u ≤ (2/3 : ℝ) then g u else h u) hf
    (lipschitz_glue_at g h hg hh (2/3) hgh) (1/3)
  rw [if_pos (by norm_num)]
  exact hfg

theorem lipschitz_interval_mul (s : I) : LipschitzWith 1 (fun t : I => s*t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |(s : ℝ)*(x : ℝ)-(s : ℝ)*(y : ℝ)| ≤ (1 : ℝ)*|(x : ℝ)-(y : ℝ)|
  rw [show (s : ℝ)*(x : ℝ)-(s : ℝ)*(y : ℝ) = (s : ℝ)*((x : ℝ)-(y : ℝ)) by ring, abs_mul,
    abs_of_nonneg s.property.1, one_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) s.property.2

theorem homotopy_trans_path_lipschitz {Z : Type*} [MetricSpace Z]
    {p q : Z} {P Q R : Path p q} {K : ℝ≥0} (F : P.Homotopy Q) (G : Q.Homotopy R)
    (hF : ∀ s, LipschitzWith K (F.eval s)) (hG : ∀ s, LipschitzWith K (G.eval s)) :
    ∀ s, LipschitzWith K ((F.trans G).eval s) := by
  intro s
  change LipschitzWith K (fun u : I => (F.trans G) (s,u))
  by_cases hs : (s : ℝ) ≤ 1/2
  · let t : I := ⟨2*(s : ℝ), ⟨by have := s.property.1; linarith, by linarith⟩⟩
    have heq : (fun u : I => (F.trans G) (s,u)) = (F.eval t : I → Z) := by
      funext u
      rw [Path.Homotopy.trans_apply, dif_pos hs]
      rfl
    rw [heq]
    exact hF t
  · let t : I := ⟨2*(s : ℝ)-1, ⟨by linarith, by have := s.property.2; linarith⟩⟩
    have heq : (fun u : I => (F.trans G) (s,u)) = (G.eval t : I → Z) := by
      funext u
      rw [Path.Homotopy.trans_apply, dif_neg hs]
      rfl
    rw [heq]
    exact hG t

namespace ControlledContraction

variable {Z : Type*} [MetricSpace Z] {p q : Z} {D J S : ℝ≥0}
variable (H : ControlledContraction p D J)

theorem shortPath_lipschitz (q : Z) : LipschitzWith D (H.shortPath q) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (H.track q).dist_le_mul (unitInterval.symm x) (unitInterval.symm y)
  have hd : dist (unitInterval.symm x) (unitInterval.symm y) = dist x y := by
    change |(1-(x : ℝ))-(1-(y : ℝ))| = |(x : ℝ)-(y : ℝ)|
    rw [show (1-(x : ℝ))-(1-(y : ℝ)) = -((x : ℝ)-(y : ℝ)) by ring, abs_neg]
  change dist (H.map (q,unitInterval.symm x)) (H.map (q,unitInterval.symm y)) ≤ D*dist x y
  rwa [hd] at h

theorem clamp_affine_lipschitz (c b : ℝ) (hc : |c| ≤ 3) :
    LipschitzWith 3 (fun u : ℝ => clampInterval (c*u+b)) := by
  simpa using lipschitz_clampInterval.comp (lipschitz_affine_le 3 c b hc)

theorem compose_clamp_lipschitz {K M : ℝ≥0} {F : I → Z}
    (hF : LipschitzWith K F) (hKM : K ≤ M) (c b : ℝ) (hc : |c| ≤ 3) :
    LipschitzWith (3*M) (fun u : ℝ => F (clampInterval (c*u+b))) := by
  have hbound : K*3 ≤ 3*M := by
    calc K*3 = 3*K := mul_comm _ _
         _ ≤ 3*M := mul_le_mul_of_nonneg_left hKM (by positivity)
  exact (hF.comp (clamp_affine_lipschitz c b hc)).weaken hbound

theorem compose_scaled_clamp_lipschitz {K M : ℝ≥0} {F : I → Z}
    (hF : LipschitzWith K F) (hKM : K ≤ M) (s : I) (c b : ℝ) (hc : |c| ≤ 3) :
    LipschitzWith (3*M) (fun u : ℝ => F (s * clampInterval (c*u+b))) := by
  apply compose_clamp_lipschitz
    (show LipschitzWith K (fun t : I => F (s*t)) from by
      simpa using hF.comp (lipschitz_interval_mul s)) hKM c b hc

theorem compressRaw_lipschitz (P : Path p q) (hP : LipschitzWith S P) (s : I) :
    LipschitzWith (3*max S D) (fun u : ℝ => compressRaw P (s,u)) := by
  have hc : |1/compressionWidth s| ≤ 3 := by
    rw [abs_of_nonneg (div_nonneg zero_le_one (compressionWidth_pos s).le)]
    apply (div_le_iff₀ (compressionWidth_pos s)).mpr
    have := compressionWidth_ge s
    linarith
  simpa only [compressRaw, add_zero, div_eq_mul_inv, one_mul, mul_comm] using
    compose_clamp_lipschitz hP (le_max_left S D) (1/compressionWidth s) 0 hc

theorem spurRaw_lipschitz (P : Path p q) (hP : LipschitzWith S P) (s : I) :
    LipschitzWith (3*max S D) (fun u : ℝ => H.spurRaw P (s,u)) := by
  unfold spurRaw slot3
  apply lipschitz_slot3
  · simpa only [add_zero] using compose_clamp_lipschitz hP (le_max_left S D) 3 0 (by norm_num)
  · exact compose_scaled_clamp_lipschitz (H.track q) (le_max_right S D) s 3 (-1) (by norm_num)
  · simpa only [neg_mul, sub_eq_add_neg, add_comm] using compose_scaled_clamp_lipschitz (H.track q) (le_max_right S D) s (-3) 3 (by norm_num)
  · norm_num [H.at_zero]
  · norm_num

theorem thirdRaw_lipschitz (P : Path p q) (hP : LipschitzWith S P) (r : I) :
    LipschitzWith (3*max S D) (fun u : ℝ => H.thirdRaw P (r,u)) := by
  unfold thirdRaw slot3
  apply lipschitz_slot3
  · simpa only [add_zero] using compose_scaled_clamp_lipschitz hP (le_max_left S D) r 3 0 (by norm_num)
  · exact compose_clamp_lipschitz (H.track (P r)) (le_max_right S D) 3 (-1) (by norm_num)
  · simpa only [neg_mul, sub_eq_add_neg, add_comm] using compose_clamp_lipschitz (H.track q) (le_max_right S D) (-3) 3 (by norm_num)
  · norm_num [H.at_zero]
  · norm_num [H.at_one]

theorem expandRaw_lipschitz (q : Z) (s : I) :
    LipschitzWith (3*max S D) (fun u : ℝ => H.expandRaw q (s,u)) := by
  have hc : |1/expansionWidth s| ≤ 3 := by
    rw [abs_of_nonneg (div_nonneg zero_le_one (expansionWidth_pos s).le)]
    apply (div_le_iff₀ (expansionWidth_pos s)).mpr
    have := expansionWidth_ge s
    linarith
  have heq : (fun u : ℝ => H.expandRaw q (s,u)) =
      (fun u : ℝ => H.shortPath q (clampInterval ((1/expansionWidth s)*u + (-pauseWidth s/expansionWidth s)))) := by
    funext u
    unfold expandRaw
    congr 2
    ring
  rw [heq]
  exact compose_clamp_lipschitz (H.shortPath_lipschitz q) (le_max_right S D) _ _ hc

/-- The path-time estimate in Lemma 5.1. The joint constant `J` does
not occur: all four stages use only the input path speed and the
contraction's time-track speed. -/
theorem relativeHomotopy_lipschitz (P : Path p q) (hP : LipschitzWith S P) :
    ∀ s, LipschitzWith (3*max S D) ((H.relativeHomotopy P).eval s) := by
  apply homotopy_trans_path_lipschitz
  · apply homotopy_trans_path_lipschitz
    · intro s
      change LipschitzWith (3*max S D) (fun u : I => compressRaw P (s,(u : ℝ)))
      simpa only [mul_one] using (compressRaw_lipschitz P hP s).comp
        (LipschitzWith.subtype_val (Set.Icc (0 : ℝ) 1))
    · intro s
      change LipschitzWith (3*max S D) (fun u : I => H.spurRaw P (s,(u : ℝ)))
      simpa only [mul_one] using (H.spurRaw_lipschitz P hP s).comp
        (LipschitzWith.subtype_val (Set.Icc (0 : ℝ) 1))
  · apply homotopy_trans_path_lipschitz
    · intro s
      change LipschitzWith (3*max S D) (fun u : I => H.thirdRaw P (unitInterval.symm s,(u : ℝ)))
      simpa only [mul_one] using (H.thirdRaw_lipschitz P hP (unitInterval.symm s)).comp
        (LipschitzWith.subtype_val (Set.Icc (0 : ℝ) 1))
    · intro s
      change LipschitzWith (3*max S D) (fun u : I => H.expandRaw q (s,(u : ℝ)))
      simpa only [mul_one] using (H.expandRaw_lipschitz (S := S) q s).comp
        (LipschitzWith.subtype_val (Set.Icc (0 : ℝ) 1))

end ControlledContraction
end
end AbelianTargets


