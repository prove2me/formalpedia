-- Prove2me | Definitions.Def_KServer_sturdy
-- name    : KServer_sturdy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T22:24:27.738371+00:00
-- url     : https://prove2.me/theorems/4011883e-ce1f-4028-ba32-81ba27dd8dc5
-- title:
--   Sturdiness invariants for chunk systems
-- statement:
--   Two forms of the sturdiness invariant for chunk systems: worst-case sturdiness (on every atom of the filtration up to depth n0, the conditional expected total is at least total - D) and L1-sturdiness (the expected positive drawdown of the Doob martingale of the total is at most D at every depth up to n0). Includes monotonicity, transfer through the parameter-weakening combinator, the depth-zero cases from a trivial initial history, and the tower/projection identity: an atom-measurable weight sees only the conditional expectation of the integrand.
-- source:
--   Bansal-Cohen-Ravi style randomized k-server lower bound

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_adjust

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

namespace ChunkSystemB

variable {X : Type*} [MetricSpace X] {s t : X}
variable {cLo cHi total price : ℝ} {mLo : ℕ}
variable (C : ChunkSystemB X s t cLo cHi total price mLo)

/-- **Sturdiness**: on every atom of the filtration up to depth `n₀`, the
conditional expected total mass is at least `total - D`.  Stated in
atom-weighted form to avoid division.  This is the invariant that removes
the variance loss from the survivor-selection step of the race: the
selection is prefix-measurable, so the surviving side's tail enters the
expected race total only through its conditional mean, which sturdiness
bounds below uniformly. -/
def Sturdy (n₀ : ℕ) (D : ℝ) : Prop :=
  ∀ n ≤ n₀, ∀ ω₀ : C.Ω,
    C.mass (C.atom n ω₀) * (total - D)
      ≤ ∑ ω ∈ C.atom n ω₀, C.P ω * C.totalSize ω

variable {C}

/-- Sturdiness weakens: smaller depth, larger defect. -/
theorem Sturdy.mono {n₀ n₀' : ℕ} {D D' : ℝ}
    (h : C.Sturdy n₀ D) (hn : n₀' ≤ n₀) (hD : D ≤ D') :
    C.Sturdy n₀' D' := by
  intro n hn' ω₀
  refine le_trans ?_ (h n (le_trans hn' hn) ω₀)
  exact mul_le_mul_of_nonneg_left (by linarith)
    (C.mass_nonneg (C.atom n ω₀))

/-- The conditional-expectation form of sturdiness. -/
theorem Sturdy.condExp_ge {n₀ : ℕ} {D : ℝ} (h : C.Sturdy n₀ D)
    {n : ℕ} (hn : n ≤ n₀) (ω₀ : C.Ω) :
    total - D ≤ C.condExp C.totalSize n ω₀ := by
  have h1 := h n hn ω₀
  have h2 := C.mass_atom_pos n ω₀
  rw [ChunkSystemB.condExp, le_div_iff₀ h2]
  linarith [h1]

/-- A system with deterministic total is sturdy with zero defect at
every depth. -/
theorem sturdy_of_const
    (hconst : ∀ ω ω' : C.Ω, C.totalSize ω = C.totalSize ω')
    (n₀ : ℕ) : C.Sturdy n₀ 0 := by
  intro n _ ω₀
  have h1 : ∀ ω ∈ C.atom n ω₀, C.P ω * C.totalSize ω
      = C.P ω * C.totalSize ω₀ := by
    intro ω _
    rw [hconst ω ω₀]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  have h2 : total - 0 ≤ C.totalSize ω₀ := by
    have h3 : total ≤ ∑ ω, C.P ω * C.totalSize ω := C.htotal
    have h4 : ∑ ω, C.P ω * C.totalSize ω = C.totalSize ω₀ := by
      rw [Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) => by
        rw [hconst ω ω₀], ← Finset.sum_mul, C.hPsum, one_mul]
    rw [h4] at h3
    linarith
  exact mul_le_mul_of_nonneg_left h2 (C.mass_nonneg _)

/-- Depth-zero sturdiness with zero defect, given a trivial initial
history. -/
theorem sturdy_zero_of_h0triv
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) :
    C.Sturdy 0 0 := by
  intro n hn ω₀
  have hn0 : n = 0 := Nat.le_zero.mp hn
  subst hn0
  have hatom : C.atom 0 ω₀ = Finset.univ := by
    ext ω
    simp only [ChunkSystemB.mem_atom, Finset.mem_univ, iff_true]
    exact h0triv ω ω₀
  rw [hatom]
  have hmass : C.mass Finset.univ = 1 := C.hPsum
  show C.mass Finset.univ * (total - 0)
      ≤ ∑ ω, C.P ω * C.totalSize ω
  rw [hmass, one_mul, sub_zero]
  exact C.htotal

/-- Sturdiness transfers through the parameter-weakening combinator. -/
theorem Sturdy.adjust {cLo' cHi' T' pe' : ℝ} {mLo' : ℕ}
    (hLo : cLo' ≤ cLo) (hHi : cHi ≤ cHi') (hT : T' ≤ total)
    (hpe : price ≤ pe') (hm : mLo' ≤ mLo)
    {n₀ : ℕ} {D : ℝ} (h : C.Sturdy n₀ D) :
    (C.adjust hLo hHi hT hpe hm).Sturdy n₀ D := by
  intro n hn ω₀
  have h1 := h n hn ω₀
  have h2 : C.mass (C.atom n ω₀) * (T' - D)
      ≤ C.mass (C.atom n ω₀) * (total - D) :=
    mul_le_mul_of_nonneg_left (by linarith) (C.mass_nonneg _)
  exact le_trans h2 h1

variable (C)

/-- The expected total mass of the system. -/
noncomputable def expTotal : ℝ := ∑ ω, C.P ω * C.totalSize ω

/-- **L¹-sturdiness**: the expected positive drawdown of the Doob
martingale of the total is at most `D` at every depth up to `n₀`.  This
is the form of sturdiness that both propagates through the race (at
shallow depths the other components are independent of the revealed
atom) and suffices for the survivor-selection bound (a selection weight
never exceeds its atom's mass). -/
def SturdyL1 (n₀ : ℕ) (D : ℝ) : Prop :=
  ∀ n ≤ n₀, ∑ ω, C.P ω
    * max (C.expTotal - C.condExp C.totalSize n ω) 0 ≤ D

variable {C}

/-- L¹-sturdiness weakens. -/
theorem SturdyL1.mono {n₀ n₀' : ℕ} {D D' : ℝ}
    (h : C.SturdyL1 n₀ D) (hn : n₀' ≤ n₀) (hD : D ≤ D') :
    C.SturdyL1 n₀' D' :=
  fun n hn' => le_trans (h n (le_trans hn' hn)) hD

/-- Depth-zero L¹-sturdiness with zero defect, given a trivial initial
history. -/
theorem sturdyL1_zero_of_h0triv
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) :
    C.SturdyL1 0 0 := by
  intro n hn
  have hn0 : n = 0 := Nat.le_zero.mp hn
  subst hn0
  have hatom : ∀ ω₀ : C.Ω, C.atom 0 ω₀ = Finset.univ := by
    intro ω₀
    ext ω
    simp only [ChunkSystemB.mem_atom, Finset.mem_univ, iff_true]
    exact h0triv ω ω₀
  have hce : ∀ ω₀ : C.Ω, C.condExp C.totalSize 0 ω₀ = C.expTotal := by
    intro ω₀
    unfold ChunkSystemB.condExp ChunkSystemB.expTotal
    rw [hatom ω₀]
    have hm1 : C.mass Finset.univ = 1 := C.hPsum
    rw [hm1, div_one]
  refine le_of_eq (Finset.sum_eq_zero fun ω _ => ?_)
  rw [hce ω, sub_self, max_self, mul_zero]

/-- The expected total is unchanged by the parameter-weakening
combinator. -/
theorem expTotal_adjust {cLo' cHi' T' pe' : ℝ} {mLo' : ℕ}
    (hLo : cLo' ≤ cLo) (hHi : cHi ≤ cHi') (hT : T' ≤ total)
    (hpe : price ≤ pe') (hm : mLo' ≤ mLo) :
    (C.adjust hLo hHi hT hpe hm).expTotal = C.expTotal := rfl

/-- L¹-sturdiness transfers through the parameter-weakening
combinator. -/
theorem SturdyL1.adjust {cLo' cHi' T' pe' : ℝ} {mLo' : ℕ}
    (hLo : cLo' ≤ cLo) (hHi : cHi ≤ cHi') (hT : T' ≤ total)
    (hpe : price ≤ pe') (hm : mLo' ≤ mLo)
    {n₀ : ℕ} {D : ℝ} (h : C.SturdyL1 n₀ D) :
    (C.adjust hLo hHi hT hpe hm).SturdyL1 n₀ D :=
  fun n hn => h n hn

/-- The tower/projection identity: an atom-measurable weight sees only
the conditional expectation. -/
theorem sum_P_mul_condExp (n : ℕ) (u f : C.Ω → ℝ)
    (hu : ∀ ω ω' : C.Ω, C.hist n ω' = C.hist n ω → u ω' = u ω) :
    ∑ ω, C.P ω * (u ω * f ω)
      = ∑ ω, C.P ω * (u ω * C.condExp f n ω) := by
  classical
  have hfib : ∀ v : C.Ω → ℝ,
      ∑ b ∈ Finset.univ.image (C.hist n),
        ∑ ω ∈ Finset.univ.filter (fun ω => C.hist n ω = b), v ω
      = ∑ ω, v ω := fun v =>
    Finset.sum_fiberwise_of_maps_to
      (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x)) v
  rw [← hfib (fun ω => C.P ω * (u ω * f ω)),
    ← hfib (fun ω => C.P ω * (u ω * C.condExp f n ω))]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_image] at hb
  obtain ⟨ω₀, -, rfl⟩ := hb
  have hfilter : Finset.univ.filter
      (fun ω => C.hist n ω = C.hist n ω₀) = C.atom n ω₀ := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ChunkSystemB.mem_atom]
  rw [hfilter]
  have hL : ∑ ω ∈ C.atom n ω₀, C.P ω * (u ω * f ω)
      = u ω₀ * ∑ ω ∈ C.atom n ω₀, C.P ω * f ω := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω hω => ?_
    rw [hu ω₀ ω (C.mem_atom.mp hω)]
    ring
  have hR : ∑ ω ∈ C.atom n ω₀, C.P ω * (u ω * C.condExp f n ω)
      = u ω₀ * (C.condExp f n ω₀ * C.mass (C.atom n ω₀)) := by
    have h1 : ∀ ω ∈ C.atom n ω₀, C.P ω * (u ω * C.condExp f n ω)
        = (u ω₀ * C.condExp f n ω₀) * C.P ω := by
      intro ω hω
      rw [hu ω₀ ω (C.mem_atom.mp hω),
        C.condExp_congr f (C.mem_atom.mp hω)]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    show u ω₀ * C.condExp f n ω₀ * C.mass (C.atom n ω₀) = _
    ring
  rw [hL, hR]
  have hmass : C.mass (C.atom n ω₀) ≠ 0 :=
    ne_of_gt (C.mass_atom_pos n ω₀)
  have hce : C.condExp f n ω₀ * C.mass (C.atom n ω₀)
      = ∑ ω ∈ C.atom n ω₀, C.P ω * f ω := by
    unfold ChunkSystemB.condExp
    rw [div_mul_cancel₀ _ hmass]
  rw [hce]

end ChunkSystemB

end KServer


