-- Prove2me | solution 1 for MissingDataCohomology.DataComplex.h1_vanishes_iff_exact
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T23:29:23.110953+00:00
-- url     : https://prove2.me/submissions/36e037fe-cf61-4de6-9f77-ee4df2b0325c

-- Sol generated from Geometry/RamseyTheory/MissingDataCohomology.lean
import Mathlib
import Definitions.Def_Geometry_FlagComplex
import Definitions.Def_Geometry_RamseyTheory_MissingDataCohomology
/-!
# Cohomological obstructions to patching incomplete data

Local observations and their overlap discrepancies form a two-step cochain
complex.  Degree-zero cocycles are globally compatible observations, while the
first cohomology is the quotient of locally consistent discrepancies by those
arising from changing local observations.  The results below give a rank formula,
a patchability criterion, and sharp boundary cases.  They also identify the
nerve's flag condition as the precise passage from pairwise overlap consistency
to higher-order faces.

-- !-- Lab Notes -- !--
Hypothesis: the obstruction space is controlled by two independent rank losses,
not by the missing rate alone; pairwise overlap data determines all higher overlap
patterns exactly when the nerve is flag.
Experiment: zero differentials give obstruction dimension `dim C¹`, whereas a
surjective first coboundary gives dimension zero at the same ambient degree.
Analysis: rank-nullity and the quotient dimension formula show
`dim H¹ = dim C¹ - rank δ⁰ - rank δ¹`.  Thus no universal function of a scalar
missing rate can determine obstruction dimension without assumptions on overlap
incidence and restriction-map ranks.
Critique: these are deterministic finite-dimensional results.  They do not justify
a probabilistic asymptotic law, a likelihood interpretation, or comparisons with
particular statistical estimators; each requires an explicit generative model.
Synthesis: the rank formula separates the two sources of information loss, the
vanishing theorem characterizes exact patchability, and the imported clique-complex
construction links pairwise consistency to the topology of the data nerve.
-- !-- Lab Notes -- !--
-/

open Finset

open MissingDataCohomology

variable (𝕜 : Type*) [Field 𝕜]


attribute [instance] DataComplex.addC0 DataComplex.addC1 DataComplex.addC2
  DataComplex.modC0 DataComplex.modC1 DataComplex.modC2 DataComplex.finC0
  DataComplex.finC1 DataComplex.finC2

variable {𝕜}

/-
Every coboundary is a cocycle.
-/
lemma DataComplex.range_d0_le_ker_d1 (D : DataComplex 𝕜) : D.d0.range ≤ D.d1.ker := by
  exact fun x hx => by obtain ⟨ y, rfl ⟩ := hx; exact LinearMap.mem_ker.2 ( LinearMap.congr_fun D.d_sq y ) ;





/-
**Cohomological information-loss formula.**  The obstruction dimension is
ambient overlap dimension minus the ranks of patch generation and consistency
checking.
-/

/-
Vanishing of first cohomology is equivalent to every cocycle being generated
by a degree-zero correction.
-/

/-
A strict rank deficit forces a nonzero patching obstruction.
-/

/-
If the first coboundary is surjective, every locally consistent discrepancy
is patchable and first cohomology vanishes.
-/

/-
For zero differentials, every overlap residual survives as an obstruction.
This boundary case shows that ambient dimensions or a missing-rate scalar alone
cannot determine cohomology.
-/

/-
**Non-identifiability from a scalar rate.**  Two data complexes can have
identically sized overlap spaces but different obstruction dimensions: zero
restriction maps retain every residual, while a surjective patch map removes
every obstruction.
-/


variable {α : Type*} [DecidableEq α]





open MissingDataCohomology in
theorem solution(D : DataComplex 𝕜) :
    Module.finrank 𝕜 D.H1 = 0 ↔ D.d1.ker = D.d0.range := by
  constructor <;> intro h;
  · -- If the finrank of H1 is zero, then the boundaries are equal to the cocycles.
    have h_eq : D.boundaries = ⊤ := by
      exact Submodule.eq_top_of_finrank_eq ( by simpa [ h ] using Submodule.finrank_quotient_add_finrank D.boundaries );
    refine' le_antisymm _ _;
    · intro x hx;
      replace h_eq := SetLike.ext_iff.mp h_eq ⟨ x, hx ⟩ ; aesop;
    · exact DataComplex.range_d0_le_ker_d1 D;
  · convert Submodule.finrank_eq_zero.mpr _;
    rotate_left;
    exact 𝕜;
    exact D.H1;
    all_goals try infer_instance;
    exact ⊤;
    · infer_instance;
    · ext x;
      obtain ⟨ y, hy ⟩ := Submodule.mkQ_surjective _ x;
      simp +decide [← hy];
      exact Submodule.mem_comap.mpr ( h ▸ y.2 );
    · simp +decide [ DataComplex.H1 ]
