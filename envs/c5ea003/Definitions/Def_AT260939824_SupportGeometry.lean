-- Prove2me | Definitions.Def_AT260939824_SupportGeometry
-- name    : AT260939824_SupportGeometry
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:46:20.791089+00:00
-- url     : https://prove2.me/theorems/fcdeb6a8-d66a-496d-86f2-d97868c10935
-- title:
--   Probability coordinates and the support complex of a finite graph
-- statement:
--   For a finite simple graph $H$ on $V$, equip probability masses with the maximum coordinate metric. A mass is supported on $A\subseteq V$ when each positive coordinate lies in $A$. Define the support complex and shore swap by
--   $$\mathcal S(H)=\{(\mu,\nu):\mu(v)>0,\nu(w)>0\Rightarrow v\sim_Hw\},\qquad
--   \tau(\mu,\nu)=(\nu,\mu).$$
--   A graph edge gives the vertex $(\delta_v,\delta_w)$. A biclique $A\times B$ gives a product-simplex carrier, on which affine interpolation in either shore stays in $\mathcal S(H)$. Interpolation defines endpoint-preserving homotopies between paths in the same carrier, including paths in a fixed-shore fiber. The canonical path for an edge of the bipartite double cover changes one shore and then the other through its prescribed corner. These constructions provide the analytic support model. For a biclique with shores $\{v,x\}$ and $\{w,y\}$, the selected square is $Q(s,t)=((1-s)\delta_v+s\delta_x,(1-t)\delta_w+t\delta_y)$. Its four corners are the corresponding edge vertices, and restricting any side gives the stated left- or right-shore affine path. Swapping a support pair interchanges its left and right projections.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/SupportGeometry.lean, selected declaration lines 34-35, 37-43, 45, 47, 49-51, 53-60, 62-63, 65, 67, 69-72, 80-93, 95-99, 101-108, 110-114, 116-117, 119-121, 123-128, 130-144, 146-151, 153-157, 163-164, 166-173, 175-181, 183-186, 188-193, 195-228, 230-231, 235-236, 238, 240-241, 243, 245-247, 249-252, 254-255, 257-258, 260-262, 264-265, 267-269, 271-272, 281-287, 308-310, 316-322, 329-333, 335-339, 341-345, 347-355, 357-379, 381-388, 401-423, 425-446, 448-455, 457-464, 466-470, 472-476, 478-486, 488-494, 496-501, 503-509, 553-556, 558-561, 563-566, 568-571, 573-578, 580-585, 587-592, 594-599; SHA-256 3601263ca4f3dc336fecf00e73a260f1ed0783868ecb8b37cb571d58f595a47c. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportModel
import Init
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

/-!
# Concrete probability support geometry

The space `SupportPair H` is the support space `𝒟(H)` in Lemma 6.2 of
arXiv:2609.39824.  Its shore swap is a free involution.  Convex interpolation
inside a fixed shore gives the graph-edge paths, and interpolation of both
shores gives the square filling for a four-walk.  These are actual continuous
maps, not assumptions about an auxiliary presentation complex.
-/

open scoped BigOperators unitInterval

namespace AbelianTargets

noncomputable section

namespace Probability

variable {V : Type*} [Fintype V]

attribute [local instance] Classical.propDecidable

instance : MetricSpace (Probability V) :=
  MetricSpace.induced mass mass_injective inferInstance

/-- The vertex of the probability simplex supported on a single vertex. -/
def dirac (v : V) : Probability V where
  mass w := if w = v then 1 else 0
  nonneg w := by split <;> norm_num
  sum_one := by
    classical
    simp

@[simp] theorem dirac_mass (v w : V) : (dirac v).mass w = if w = v then 1 else 0 := rfl

@[simp] theorem dirac_mass_self (v : V) : (dirac v).mass v = 1 := by simp

theorem dirac_mass_pos_iff (v w : V) : 0 < (dirac v).mass w ↔ w = v := by
  classical
  by_cases h : w = v <;> simp [h]

/-- Affine interpolation, with parameter in the closed unit interval. -/
def mix (p q : Probability V) (t : I) : Probability V where
  mass v := (1 - (t : ℝ)) * p.mass v + (t : ℝ) * q.mass v
  nonneg v := add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (p.nonneg v))
    (mul_nonneg t.property.1 (q.nonneg v))
  sum_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, p.sum_one, q.sum_one]
    ring

@[simp] theorem mix_mass (p q : Probability V) (t : I) (v : V) :
    (mix p q t).mass v = (1 - (t : ℝ)) * p.mass v + (t : ℝ) * q.mass v := rfl

@[simp] theorem mix_zero (p q : Probability V) : mix p q 0 = p := by ext; simp

@[simp] theorem mix_one (p q : Probability V) : mix p q 1 = q := by ext; simp

@[simp] theorem mix_self (p : Probability V) (t : I) : mix p p t = p := by
  ext v
  simp only [mix_mass]
  ring



theorem continuous_mix :
    Continuous (fun z : (Probability V × Probability V) × I => mix z.1.1 z.1.2 z.2) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro v
  change Continuous (fun z : (Probability V × Probability V) × I =>
    (1 - (z.2 : ℝ)) * z.1.1.mass v + (z.2 : ℝ) * z.1.2.mass v)
  have ht : Continuous (fun z : (Probability V × Probability V) × I => (z.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hp : Continuous (fun z : (Probability V × Probability V) × I => z.1.1.mass v) :=
    (continuous_mass_apply v).comp (continuous_fst.comp continuous_fst)
  have hq : Continuous (fun z : (Probability V × Probability V) × I => z.1.2.mass v) :=
    (continuous_mass_apply v).comp (continuous_snd.comp continuous_fst)
  exact ((continuous_const.sub ht).mul hp).add (ht.mul hq)

theorem continuous_mix_of_continuous {X : Type*} [TopologicalSpace X]
    {p q : X → Probability V} {t : X → I}
    (hp : Continuous p) (hq : Continuous q) (ht : Continuous t) :
    Continuous (fun x => mix (p x) (q x) (t x)) :=
  continuous_mix.comp ((hp.prodMk hq).prodMk ht)

/-- Positive mass in a convex interpolation must occur in at least one endpoint. -/
theorem mix_pos_imp (p q : Probability V) (t : I) (v : V)
    (h : 0 < (mix p q t).mass v) : 0 < p.mass v ∨ 0 < q.mass v := by
  by_contra hn
  push Not at hn
  have hp : p.mass v = 0 := le_antisymm hn.1 (p.nonneg v)
  have hq : q.mass v = 0 := le_antisymm hn.2 (q.nonneg v)
  simp [hp, hq] at h

theorem mass_le_one (p : Probability V) (v : V) : p.mass v ≤ 1 := by
  classical
  calc
    p.mass v ≤ ∑ w, p.mass w := Finset.single_le_sum (fun w _ => p.nonneg w) (Finset.mem_univ v)
    _ = 1 := p.sum_one

/-- Every positive coordinate lies in the specified face. -/
def SupportedOn (p : Probability V) (A : Set V) : Prop := ∀ v, 0 < p.mass v → v ∈ A

theorem supportedOn_dirac (v : V) {A : Set V} (hv : v ∈ A) : SupportedOn (dirac v) A := by
  intro w hw
  rwa [dirac_mass_pos_iff v w |>.mp hw]

theorem supportedOn_mix {p q : Probability V} {A : Set V}
    (hp : SupportedOn p A) (hq : SupportedOn q A) (t : I) : SupportedOn (mix p q t) A := by
  intro v hv
  rcases mix_pos_imp p q t v hv with h | h
  · exact hp v h
  · exact hq v h

/-- The probability simplex is a closed subset of its ambient coordinate space. -/
theorem isClosed_range_mass : IsClosed (Set.range (mass : Probability V → V → ℝ)) := by
  have hrange : Set.range (mass : Probability V → V → ℝ) =
      {m | (∀ v, 0 ≤ m v) ∧ ∑ v, m v = 1} := by
    ext m
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.nonneg, p.sum_one⟩
    · rintro ⟨hn, hs⟩
      exact ⟨⟨m, hn, hs⟩, rfl⟩
  rw [hrange]
  have hn : IsClosed {m : V → ℝ | ∀ v, 0 ≤ m v} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun v => isClosed_le continuous_const (continuous_apply v))
  exact hn.inter (isClosed_eq (continuous_finsetSum _ (fun v _ => continuous_apply v)) continuous_const)

theorem isCompact_range_mass : IsCompact (Set.range (mass : Probability V → V → ℝ)) := by
  have hbox : IsCompact (Set.pi Set.univ (fun _ : V => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ : V => (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)))
  apply hbox.of_isClosed_subset isClosed_range_mass
  rintro m ⟨p, rfl⟩
  exact fun v _ => ⟨p.nonneg v, p.mass_le_one v⟩

instance : CompactSpace (Probability V) := by
  apply isCompact_univ_iff.mp
  have hi : Topology.IsInducing (mass : Probability V → V → ℝ) := ⟨rfl⟩
  apply hi.isCompact_iff.mpr
  simpa using isCompact_range_mass (V := V)

end Probability

variable {V : Type*} [Fintype V] (H : SimpleGraph V)

theorem compatible_symm {p q : Probability V} (h : Compatible H p q) :
    Compatible H q p := fun u v hu hv => (h v u hv hu).symm

theorem compatible_dirac {u v : V} (h : H.Adj u v) :
    Compatible H (Probability.dirac u) (Probability.dirac v) := by
  intro a b ha hb
  have ha' := Probability.dirac_mass_pos_iff u a |>.mp ha
  have hb' := Probability.dirac_mass_pos_iff v b |>.mp hb
  subst a
  subst b
  exact h

theorem compatible_mix_left {p r q : Probability V}
    (hp : Compatible H p q) (hr : Compatible H r q) (t : I) :
    Compatible H (Probability.mix p r t) q := by
  intro u v hu hv
  rcases Probability.mix_pos_imp p r t u hu with h | h
  · exact hp u v h hv
  · exact hr u v h hv

theorem compatible_mix_right {p q s : Probability V}
    (hq : Compatible H p q) (hs : Compatible H p s) (t : I) :
    Compatible H p (Probability.mix q s t) :=
  compatible_symm H (compatible_mix_left H (compatible_symm H hq) (compatible_symm H hs) t)

theorem compatible_mix_rectangle {p r q s : Probability V}
    (hpq : Compatible H p q) (hps : Compatible H p s)
    (hrq : Compatible H r q) (hrs : Compatible H r s) (t u : I) :
    Compatible H (Probability.mix p r t) (Probability.mix q s u) :=
  compatible_mix_right H (compatible_mix_left H hpq hrq t)
    (compatible_mix_left H hps hrs t) u

/-- The support condition is closed: a nonedge forces a zero coordinate on
at least one of the two shores. -/
theorem isClosed_compatible :
    IsClosed {pq : Probability V × Probability V | Compatible H pq.1 pq.2} := by
  classical
  have heq : {pq : Probability V × Probability V | Compatible H pq.1 pq.2} =
      ⋂ u : V, ⋂ v : V, {pq | H.Adj u v ∨ pq.1.mass u = 0 ∨ pq.2.mass v = 0} := by
    ext pq
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h u v
      by_cases hu : pq.1.mass u = 0
      · exact Or.inr (Or.inl hu)
      by_cases hv : pq.2.mass v = 0
      · exact Or.inr (Or.inr hv)
      exact Or.inl (h u v (lt_of_le_of_ne (pq.1.nonneg u) (Ne.symm hu))
        (lt_of_le_of_ne (pq.2.nonneg v) (Ne.symm hv)))
    · intro h u v hu hv
      rcases h u v with he | he | he
      · exact he
      · rw [he] at hu
        exact (lt_irrefl 0 hu).elim
      · rw [he] at hv
        exact (lt_irrefl 0 hv).elim
  rw [heq]
  apply isClosed_iInter
  intro u
  apply isClosed_iInter
  intro v
  by_cases h : H.Adj u v
  · simp [h]
  · simp only [h, false_or]
    exact (isClosed_eq ((Probability.continuous_mass_apply u).comp continuous_fst) continuous_const).union
      (isClosed_eq ((Probability.continuous_mass_apply v).comp continuous_snd) continuous_const)

/-- The compact support complex `𝒟(H)` in probability coordinates. -/
def SupportPair := {pq : Probability V × Probability V // Compatible H pq.1 pq.2}

namespace SupportPair

instance : TopologicalSpace (SupportPair H) := inferInstanceAs (TopologicalSpace (Subtype _))
instance : MetricSpace (SupportPair H) := inferInstanceAs (MetricSpace (Subtype _))

instance : CompactSpace (SupportPair H) := isCompact_iff_compactSpace.mp (isClosed_compatible H).isCompact

def left (z : SupportPair H) : Probability V := z.val.1
def right (z : SupportPair H) : Probability V := z.val.2

theorem compatible (z : SupportPair H) : Compatible H z.left z.right := z.property

/-- A product of two simplex faces inside the support complex. -/
def InCarrier (A B : Set V) (z : SupportPair H) : Prop :=
  z.left.SupportedOn A ∧ z.right.SupportedOn B

theorem compatible_of_carrier {A B : Set V}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b)
    {z w : SupportPair H} (hz : InCarrier H A B z) (hw : InCarrier H A B w) :
    Compatible H z.left w.right := fun a b ha hb => hAB a (hz.1 a ha) b (hw.2 b hb)

theorem continuous_left : Continuous (left H : SupportPair H → Probability V) :=
  continuous_fst.comp continuous_subtype_val

theorem continuous_right : Continuous (right H : SupportPair H → Probability V) :=
  continuous_snd.comp continuous_subtype_val

/-- Swap of the two probability shores. -/
def swap (z : SupportPair H) : SupportPair H :=
  ⟨(z.right, z.left), compatible_symm H z.compatible⟩

@[simp] theorem swap_left (z : SupportPair H) : (swap H z).left = z.right := rfl
@[simp] theorem swap_right (z : SupportPair H) : (swap H z).right = z.left := rfl

@[simp] theorem swap_swap (z : SupportPair H) : swap H (swap H z) = z := by
  apply Subtype.ext
  rfl

theorem continuous_swap : Continuous (swap H) :=
  (continuous_right H |>.prodMk (continuous_left H)).subtype_mk _



/-- The actual support complex supplies the analytic support model. -/
def model : SupportModel H (swap H) where
  p := left H
  q := right H
  continuous_p := continuous_left H
  compatible := compatible H
  first_swap _ := rfl





/-- A support pair concentrated on the ends of a graph edge. -/
def vertex {u v : V} (h : H.Adj u v) : SupportPair H :=
  ⟨(Probability.dirac u, Probability.dirac v), compatible_dirac H h⟩



/-- Convex interpolation of both shores inside a common biclique carrier. -/
def carrierMix {A B : Set V} (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b)
    (z w : SupportPair H) (hz : InCarrier H A B z) (hw : InCarrier H A B w)
    (t : I) : SupportPair H :=
  ⟨(Probability.mix z.left w.left t, Probability.mix z.right w.right t),
    compatible_mix_rectangle H z.compatible (compatible_of_carrier H hAB hz hw)
      (compatible_of_carrier H hAB hw hz) w.compatible t t⟩



@[simp] theorem carrierMix_zero {A B : Set V} (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b)
    (z w : SupportPair H) (hz : InCarrier H A B z) (hw : InCarrier H A B w) :
    carrierMix H hAB z w hz hw 0 = z := by
  apply Subtype.ext
  simp [carrierMix, left, right]

@[simp] theorem carrierMix_one {A B : Set V} (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b)
    (z w : SupportPair H) (hz : InCarrier H A B z) (hw : InCarrier H A B w) :
    carrierMix H hAB z w hz hw 1 = w := by
  apply Subtype.ext
  simp [carrierMix, left, right]

@[simp] theorem carrierMix_self {A B : Set V} (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b)
    (z : SupportPair H) (hz hw : InCarrier H A B z) (t : I) :
    carrierMix H hAB z z hz hw t = z := by
  apply Subtype.ext
  simp [carrierMix, left, right]

theorem continuous_carrierMix {A B : Set V} (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b)
    {X : Type*} [TopologicalSpace X] {z w : X → SupportPair H} {t : X → I}
    (hz : ∀ x, InCarrier H A B (z x)) (hw : ∀ x, InCarrier H A B (w x))
    (hzc : Continuous z) (hwc : Continuous w) (htc : Continuous t) :
    Continuous (fun x => carrierMix H hAB (z x) (w x) (hz x) (hw x) (t x)) :=
  ((Probability.continuous_mix_of_continuous ((continuous_left H).comp hzc)
      ((continuous_left H).comp hwc) htc).prodMk
    (Probability.continuous_mix_of_continuous ((continuous_right H).comp hzc)
      ((continuous_right H).comp hwc) htc)).subtype_mk _

/-- Any two paths with the same endpoints in one product-simplex carrier
are homotopic relative to the endpoints by affine interpolation. -/
def carrierHomotopy {A B : Set V} (hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b)
    {z₀ z₁ : SupportPair H} (P Q : Path z₀ z₁)
    (hP : ∀ t, InCarrier H A B (P t)) (hQ : ∀ t, InCarrier H A B (Q t)) :
    P.Homotopy Q where
  toFun st := carrierMix H hAB (P st.2) (Q st.2) (hP st.2) (hQ st.2) st.1
  continuous_toFun := continuous_carrierMix H hAB _ _
    (P.continuous.comp continuous_snd) (Q.continuous.comp continuous_snd) continuous_fst
  map_zero_left t := carrierMix_zero H hAB (P t) (Q t) (hP t) (hQ t)
  map_one_left t := carrierMix_one H hAB (P t) (Q t) (hP t) (hQ t)
  prop' := by
    intro s t ht
    rcases ht with ht | ht
    · subst t
      change carrierMix H hAB (P 0) (Q 0) (hP 0) (hQ 0) s = P 0
      simp only [Path.source]
      exact carrierMix_self H hAB _ _ _ s
    · simp only [Set.mem_singleton_iff] at ht
      subst t
      change carrierMix H hAB (P 1) (Q 1) (hP 1) (hQ 1) s = P 1
      simp only [Path.target]
      exact carrierMix_self H hAB _ _ _ s

theorem inCarrier_trans {A B : Set V} {z₀ z₁ z₂ : SupportPair H}
    (P : Path z₀ z₁) (Q : Path z₁ z₂)
    (hP : ∀ t, InCarrier H A B (P t)) (hQ : ∀ t, InCarrier H A B (Q t)) (t : I) :
    InCarrier H A B (P.trans Q t) := by
  rw [Path.trans_apply]
  split_ifs
  · exact hP _
  · exact hQ _





/-- The contractibility of a fixed second-shore fiber, in the relative-path
form needed when the chosen-neighbor detours of graph edges are removed. -/
def fixedRightHomotopy {z₀ z₁ : SupportPair H} (P Q : Path z₀ z₁)
    (q : Probability V) (hP : ∀ t, (P t).right = q) (hQ : ∀ t, (Q t).right = q) :
    P.Homotopy Q := by
  let A : Set V := {a | ∀ b, 0 < q.mass b → H.Adj a b}
  let B : Set V := {b | 0 < q.mass b}
  have hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b := fun a ha b hb => ha b hb
  have hp : ∀ t, InCarrier H A B (P t) := by
    intro t
    constructor
    · intro a ha b hb
      exact compatible H (P t) a b ha (by simpa [hP t] using hb)
    · intro b hb
      simpa [B, hP t] using hb
  have hq : ∀ t, InCarrier H A B (Q t) := by
    intro t
    constructor
    · intro a ha b hb
      exact compatible H (Q t) a b ha (by simpa [hQ t] using hb)
    · intro b hb
      simpa [B, hQ t] using hb
  exact carrierHomotopy H hAB P Q hp hq

/-- The corresponding fixed first-shore relative path contraction. -/
def fixedLeftHomotopy {z₀ z₁ : SupportPair H} (P Q : Path z₀ z₁)
    (p : Probability V) (hP : ∀ t, (P t).left = p) (hQ : ∀ t, (Q t).left = p) :
    P.Homotopy Q := by
  let A : Set V := {a | 0 < p.mass a}
  let B : Set V := {b | ∀ a, 0 < p.mass a → H.Adj a b}
  have hAB : ∀ a ∈ A, ∀ b ∈ B, H.Adj a b := fun a ha b hb => hb a ha
  have hp : ∀ t, InCarrier H A B (P t) := by
    intro t
    constructor
    · intro a ha
      simpa [A, hP t] using ha
    · intro b hb a ha
      exact compatible H (P t) a b (by simpa [hP t] using ha) hb
  have hq : ∀ t, InCarrier H A B (Q t) := by
    intro t
    constructor
    · intro a ha
      simpa [A, hQ t] using ha
    · intro b hb a ha
      exact compatible H (Q t) a b (by simpa [hQ t] using ha) hb
  exact carrierHomotopy H hAB P Q hp hq

/-- Convex interpolation in the first shore with the second shore fixed. -/
def leftPath {p r q : Probability V} (hp : Compatible H p q) (hr : Compatible H r q) :
    Path (⟨(p, q), hp⟩ : SupportPair H) ⟨(r, q), hr⟩ where
  toFun t := ⟨(Probability.mix p r t, q), compatible_mix_left H hp hr t⟩
  continuous_toFun := (Probability.continuous_mix_of_continuous
    continuous_const continuous_const continuous_id |>.prodMk continuous_const).subtype_mk _
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp

/-- Convex interpolation in the second shore with the first shore fixed. -/
def rightPath {p q s : Probability V} (hq : Compatible H p q) (hs : Compatible H p s) :
    Path (⟨(p, q), hq⟩ : SupportPair H) ⟨(p, s), hs⟩ where
  toFun t := ⟨(p, Probability.mix q s t), compatible_mix_right H hq hs t⟩
  continuous_toFun := (continuous_const.prodMk (Probability.continuous_mix_of_continuous
    continuous_const continuous_const continuous_id)).subtype_mk _
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp

theorem leftPath_inCarrier {A B : Set V} {p r q : Probability V}
    (hp : Compatible H p q) (hr : Compatible H r q)
    (hpA : p.SupportedOn A) (hrA : r.SupportedOn A) (hqB : q.SupportedOn B) (t : I) :
    InCarrier H A B (leftPath H hp hr t) :=
  ⟨Probability.supportedOn_mix hpA hrA t, hqB⟩

theorem rightPath_inCarrier {A B : Set V} {p q s : Probability V}
    (hq : Compatible H p q) (hs : Compatible H p s)
    (hpA : p.SupportedOn A) (hqB : q.SupportedOn B) (hsB : s.SupportedOn B) (t : I) :
    InCarrier H A B (rightPath H hq hs t) :=
  ⟨hpA, Probability.supportedOn_mix hqB hsB t⟩

/-- Removing an intermediate point in a fixed-shore fiber is a genuine
endpoint-preserving homotopy. -/
theorem leftPath_trans_homotopic {p r s q : Probability V}
    (hp : Compatible H p q) (hr : Compatible H r q) (hs : Compatible H s q) :
    ((leftPath H hp hr).trans (leftPath H hr hs)).Homotopic (leftPath H hp hs) := by
  refine ⟨fixedRightHomotopy H _ _ q ?_ (fun _ => rfl)⟩
  intro t
  exact (congrArg (right H) (Path.trans_apply (leftPath H hp hr) (leftPath H hr hs) t)).trans
    (by split_ifs <;> rfl)

theorem rightPath_trans_homotopic {p q r s : Probability V}
    (hq : Compatible H p q) (hr : Compatible H p r) (hs : Compatible H p s) :
    ((rightPath H hq hr).trans (rightPath H hr hs)).Homotopic (rightPath H hq hs) := by
  refine ⟨fixedLeftHomotopy H _ _ p ?_ (fun _ => rfl)⟩
  intro t
  exact (congrArg (left H) (Path.trans_apply (rightPath H hq hr) (rightPath H hr hs) t)).trans
    (by split_ifs <;> rfl)

/-- A bipartite-double-cover edge, routed through its canonical corner. -/
def doubleEdgePath {u u' v v' : V}
    (hu : H.Adj u u') (huv : H.Adj u v) (hv : H.Adj v' v) :
    Path (vertex H hu) (vertex H hv) :=
  (rightPath H (compatible_dirac H hu) (compatible_dirac H huv)).trans
    (leftPath H (compatible_dirac H huv) (compatible_dirac H hv))

/-- Product-simplex filling for the four-walk `v-w-x-y-v`. -/
def square {v w x y : V} (hvw : H.Adj v w) (hxw : H.Adj x w)
    (hxy : H.Adj x y) (hvy : H.Adj v y) : I × I → SupportPair H :=
  fun t => ⟨(Probability.mix (Probability.dirac v) (Probability.dirac x) t.1,
    Probability.mix (Probability.dirac w) (Probability.dirac y) t.2),
    compatible_mix_rectangle H (compatible_dirac H hvw) (compatible_dirac H hvy)
      (compatible_dirac H hxw) (compatible_dirac H hxy) t.1 t.2⟩







@[simp] theorem square_zero_zero {v w x y : V} (hvw : H.Adj v w) (hxw : H.Adj x w)
    (hxy : H.Adj x y) (hvy : H.Adj v y) : square H hvw hxw hxy hvy (0, 0) = vertex H hvw := by
  apply Subtype.ext
  simp [square, vertex]

@[simp] theorem square_one_zero {v w x y : V} (hvw : H.Adj v w) (hxw : H.Adj x w)
    (hxy : H.Adj x y) (hvy : H.Adj v y) : square H hvw hxw hxy hvy (1, 0) = vertex H hxw := by
  apply Subtype.ext
  simp [square, vertex]

@[simp] theorem square_one_one {v w x y : V} (hvw : H.Adj v w) (hxw : H.Adj x w)
    (hxy : H.Adj x y) (hvy : H.Adj v y) : square H hvw hxw hxy hvy (1, 1) = vertex H hxy := by
  apply Subtype.ext
  simp [square, vertex]

@[simp] theorem square_zero_one {v w x y : V} (hvw : H.Adj v w) (hxw : H.Adj x w)
    (hxy : H.Adj x y) (hvy : H.Adj v y) : square H hvw hxw hxy hvy (0, 1) = vertex H hvy := by
  apply Subtype.ext
  simp [square, vertex]

@[simp] theorem square_bottom {v w x y : V} (hvw : H.Adj v w) (hxw : H.Adj x w)
    (hxy : H.Adj x y) (hvy : H.Adj v y) (t : I) :
    square H hvw hxw hxy hvy (t, 0) =
      leftPath H (compatible_dirac H hvw) (compatible_dirac H hxw) t := by
  apply Subtype.ext
  simp [square, leftPath]

@[simp] theorem square_top {v w x y : V} (hvw : H.Adj v w) (hxw : H.Adj x w)
    (hxy : H.Adj x y) (hvy : H.Adj v y) (t : I) :
    square H hvw hxw hxy hvy (t, 1) =
      leftPath H (compatible_dirac H hvy) (compatible_dirac H hxy) t := by
  apply Subtype.ext
  simp [square, leftPath]

@[simp] theorem square_left {v w x y : V} (hvw : H.Adj v w) (hxw : H.Adj x w)
    (hxy : H.Adj x y) (hvy : H.Adj v y) (t : I) :
    square H hvw hxw hxy hvy (0, t) =
      rightPath H (compatible_dirac H hvw) (compatible_dirac H hvy) t := by
  apply Subtype.ext
  simp [square, rightPath]

@[simp] theorem square_right {v w x y : V} (hvw : H.Adj v w) (hxw : H.Adj x w)
    (hxy : H.Adj x y) (hvy : H.Adj v y) (t : I) :
    square H hvw hxw hxy hvy (1, t) =
      rightPath H (compatible_dirac H hxw) (compatible_dirac H hxy) t := by
  apply Subtype.ext
  simp [square, rightPath]

end SupportPair

end

end AbelianTargets


