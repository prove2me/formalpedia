-- Prove2me | Definitions.Def_KServer_prophecy
-- name    : KServer_prophecy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-02T00:06:23.827511+00:00
-- url     : https://prove2.me/theorems/a8d7dbe7-a0b6-41b0-b152-8f2c86c0863d
-- title:
--   Partitioned prophecy energy and the block-variance discharge
-- statement:
--   The partitioned prophecy energy of a chunk system, and the discharge of the conditional-block-variance budget. Since chunk sizes are adapted (each size is measurable in the history at its own index), every Doob increment of the total is a revision of the conditional expectation of FUTURE sizes. For a partition of the chunk range by monotone deterministic boundaries e_0 = 0 <= e_1 <= ... <= e_K = m, the prophecy energy is the sum over cells [e_k, e_{k+1}) and depths h in the cell of the second moment of the Doob increment at h of the tail mass beyond the cell's end e_{k+1}: the energy of predicting what lies beyond the current cell. ProphecyBound PE asserts this is at most PE for every partition. The main theorem cv_from_ppe discharges the conditional block-variance hypothesis of the fixed-block regrouping: each block's conditional variance equals its interval Doob energy (orthogonal increments); each within-block increment of the block mass is the increment of the full total minus the increment of the beyond-block tail (the prefix increment vanishes by adaptedness); the total's energy over the partition telescopes to its variance (at most V, using the trivial initial history), and the tail terms are the prophecy energy (at most PE). Hence the block-variance budget is at most 2V + 2PE. Auxiliary lemmas: orthogonality of conditionally-centred one-step-measurable increment families, interval energy identities, and linearity/vanishing of Doob increments.
-- source:
--   Bartal-Chrobak-Rasala lower bound program: prophecy energy

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_chunk_var
import Definitions.Def_KServer_sturdy

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace KServer

namespace ChunkSystemB

variable {X : Type*} [MetricSpace X] {s t : X}
variable {cLo cHi total price : ℝ} {mLo : ℕ}
variable {C : ChunkSystemB X s t cLo cHi total price mLo}

/-- The tail mass from position `j` on. -/
noncomputable def tailSum (C : ChunkSystemB X s t cLo cHi total price mLo)
    (j : ℕ) (ω : C.Ω) : ℝ :=
  ∑ i ∈ Finset.Ico j C.m, C.sizeN i ω

/-- **Partitioned prophecy energy bound**: for every partition of the
chunk range by monotone boundaries, the summed second moments of the
Doob increments of the partition-cell *tail* masses — the energy of
predicting what lies beyond the current cell's end — are at most `PE`.
Since sizes are adapted, this is the part of the filtration's revelation
that reaches beyond the current cell, and it is exactly what controls
the conditional block variances of a fixed-block regrouping. -/
def ProphecyBound (C : ChunkSystemB X s t cLo cHi total price mLo)
    (PE : ℝ) : Prop :=
  ∀ (K : ℕ) (e : ℕ → ℕ), e 0 = 0 → (∀ k, e k ≤ e (k + 1)) → e K = C.m →
    ∑ k ∈ Finset.range K, ∑ h ∈ Finset.Ico (e k) (e (k + 1)),
      ∑ ω, C.P ω * (C.dinc (C.tailSum (e (k + 1))) h ω) ^ 2 ≤ PE

/-- The prophecy bound weakens. -/
theorem ProphecyBound.mono {PE PE' : ℝ} (h : C.ProphecyBound PE)
    (hPE : PE ≤ PE') : C.ProphecyBound PE' :=
  fun K e he0 hemono heK => le_trans (h K e he0 hemono heK) hPE

/-- The conditional expectation of a time-`h` measurable function is the
function itself. -/
theorem condExp_of_meas' {f : C.Ω → ℝ} {h : ℕ} {ω : C.Ω}
    (hf : ∀ ω', C.hist h ω' = C.hist h ω → f ω' = f ω) :
    C.condExp f h ω = f ω := by
  unfold ChunkSystemB.condExp
  have h1 : ∑ ω' ∈ C.atom h ω, C.P ω' * f ω'
      = f ω * C.mass (C.atom h ω) := by
    unfold ChunkSystemB.mass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω' hm => ?_
    rw [hf ω' (C.mem_atom.mp hm)]
    ring
  rw [h1, mul_div_assoc, div_self (ne_of_gt (C.mass_atom_pos h ω)), mul_one]

/-- Doob increments are conditionally centred. -/
theorem condExp_dinc_zero (f : C.Ω → ℝ) (h : ℕ) (ω : C.Ω) :
    C.condExp (C.dinc f h) h ω = 0 := by
  unfold ChunkSystemB.dinc
  rw [C.condExp_sub, C.condExp_condExp (Nat.le_succ h),
    C.condExp_condExp (le_refl h), sub_self]

/-- Doob increments are measurable one step later. -/
theorem dinc_meas (f : C.Ω → ℝ) (h : ℕ) {ω ω' : C.Ω}
    (hh : C.hist (h + 1) ω' = C.hist (h + 1) ω) :
    C.dinc f h ω' = C.dinc f h ω := by
  unfold ChunkSystemB.dinc
  rw [C.condExp_congr f hh,
    C.condExp_congr f (C.href h (h + 1) (Nat.le_succ h) ω' ω hh)]

/-- **Orthogonality over an index set**: a family of increments, each
measurable one step after its index and conditionally centred at its
index, has additive second moments. -/
theorem sq_sum_orth (W : ℕ → C.Ω → ℝ) (sset : Finset ℕ)
    (hmeas : ∀ h ∈ sset, ∀ ω ω' : C.Ω,
      C.hist (h + 1) ω' = C.hist (h + 1) ω → W h ω' = W h ω)
    (hzero : ∀ h ∈ sset, ∀ ω, C.condExp (W h) h ω = 0) :
    ∑ ω, C.P ω * (∑ h ∈ sset, W h ω) ^ 2
      = ∑ h ∈ sset, ∑ ω, C.P ω * W h ω ^ 2 := by
  have hcross : ∀ h ∈ sset, ∀ h' ∈ sset, h < h' →
      ∑ ω, C.P ω * (W h ω * W h' ω) = 0 := by
    intro h hm h' hm' hlt
    have hu : ∀ ω ω' : C.Ω, C.hist h' ω' = C.hist h' ω →
        W h ω' = W h ω := fun ω ω' hh =>
      hmeas h hm ω ω' (C.href (h + 1) h' (by omega) ω' ω hh)
    rw [sum_P_mul_condExp h' (W h) (W h') hu]
    refine Finset.sum_eq_zero fun ω _ => ?_
    rw [hzero h' hm' ω, mul_zero, mul_zero]
  have hexp : ∑ ω, C.P ω * (∑ h ∈ sset, W h ω) ^ 2
      = ∑ h ∈ sset, ∑ h' ∈ sset, ∑ ω, C.P ω * (W h ω * W h' ω) := by
    have h1 : ∀ ω : C.Ω, C.P ω * (∑ h ∈ sset, W h ω) ^ 2
        = ∑ h ∈ sset, ∑ h' ∈ sset, C.P ω * (W h ω * W h' ω) := by
      intro ω
      rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun ω _ => h1 ω, Finset.sum_comm]
    exact Finset.sum_congr rfl fun h _ => Finset.sum_comm
  rw [hexp]
  refine Finset.sum_congr rfl fun h hm => ?_
  rw [Finset.sum_eq_single h]
  · refine Finset.sum_congr rfl fun ω _ => ?_
    rw [pow_two]
  · intro h' hm' hne
    rcases Nat.lt_or_ge h h' with hlt | hge
    · exact hcross h hm h' hm' hlt
    · have hlt' : h' < h := by omega
      rw [← hcross h' hm' h hm hlt']
      exact Finset.sum_congr rfl fun ω _ => by ring
  · intro hc
    exact absurd hm hc

/-- **Interval energy**: the conditional variance of a function
measurable at the interval's end, given the interval's start, is the
summed energy of its Doob increments across the interval. -/
theorem interval_energy (f : C.Ω → ℝ) {a b : ℕ} (hab : a ≤ b)
    (hmeas : ∀ ω ω' : C.Ω, C.hist b ω' = C.hist b ω → f ω' = f ω) :
    ∑ ω, C.P ω * (f ω - C.condExp f a ω) ^ 2
      = ∑ h ∈ Finset.Ico a b, ∑ ω, C.P ω * (C.dinc f h ω) ^ 2 := by
  have htel : ∀ ω : C.Ω, f ω - C.condExp f a ω
      = ∑ h ∈ Finset.Ico a b, C.dinc f h ω := by
    intro ω
    have h1 : ∑ h ∈ Finset.Ico a b, C.dinc f h ω
        = ∑ h ∈ Finset.range b, C.dinc f h ω
          - ∑ h ∈ Finset.range a, C.dinc f h ω := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive (fun h => C.dinc f h ω)
          (Nat.zero_le a) hab]
      ring
    have h2 : ∀ n : ℕ, ∑ h ∈ Finset.range n, C.dinc f h ω
        = C.condExp f n ω - C.condExp f 0 ω := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        unfold ChunkSystemB.dinc
        ring
    have h3 : C.condExp f b ω = f ω :=
      condExp_of_meas' fun ω' hh => hmeas ω ω' hh
    rw [h1, h2 b, h2 a, h3]
    ring
  rw [Finset.sum_congr rfl fun ω _ => by rw [htel ω]]
  exact sq_sum_orth (fun h => C.dinc f h) (Finset.Ico a b)
    (fun h _ ω ω' hh => dinc_meas f h hh)
    (fun h _ ω => condExp_dinc_zero f h ω)

/-- Doob increments of a start-measurable summand vanish. -/
theorem dinc_of_meas {f : C.Ω → ℝ} {a h : ℕ} (hah : a ≤ h)
    (hf : ∀ ω ω' : C.Ω, C.hist a ω' = C.hist a ω → f ω' = f ω)
    (ω : C.Ω) : C.dinc f h ω = 0 := by
  unfold ChunkSystemB.dinc
  have h1 : C.condExp f h ω = f ω :=
    condExp_of_meas' fun ω' hh =>
      hf ω ω' (C.href a h hah ω' ω hh)
  have h2 : C.condExp f (h + 1) ω = f ω :=
    condExp_of_meas' fun ω' hh =>
      hf ω ω' (C.href a (h + 1) (by omega) ω' ω hh)
  rw [h1, h2, sub_self]

/-- Doob increments are additive in the function. -/
theorem dinc_add (f g : C.Ω → ℝ) (h : ℕ) (ω : C.Ω) :
    C.dinc (fun ω' => f ω' + g ω') h ω = C.dinc f h ω + C.dinc g h ω := by
  unfold ChunkSystemB.dinc
  have h1 : ∀ n : ℕ, C.condExp (fun ω' => f ω' + g ω') n ω
      = C.condExp f n ω + C.condExp g n ω := by
    intro n
    have := C.condExp_sub f (fun ω' => - g ω') n ω
    have h2 : C.condExp (fun ω' => f ω' - - g ω') n ω
        = C.condExp (fun ω' => f ω' + g ω') n ω :=
      C.condExp_congr_fun fun ω' _ => by ring
    have h3 : C.condExp (fun ω' => - g ω') n ω
        = 0 - C.condExp g n ω := by
      have h4 := C.condExp_sub (fun _ => (0 : ℝ)) g n ω
      have h5 : C.condExp (fun ω' => (0 : ℝ) - g ω') n ω
          = C.condExp (fun ω' => - g ω') n ω :=
        C.condExp_congr_fun fun ω' _ => by ring
      rw [← h5, h4, C.condExp_const]
    rw [← h2, this, h3]
    ring
  rw [h1, h1]
  ring

/-- Doob increments respect pointwise equality. -/
theorem dinc_congr_fun {f g : C.Ω → ℝ} (hfg : ∀ ω, f ω = g ω)
    (h : ℕ) (ω : C.Ω) : C.dinc f h ω = C.dinc g h ω := by
  unfold ChunkSystemB.dinc
  rw [C.condExp_congr_fun fun ω' _ => hfg ω',
    C.condExp_congr_fun fun ω' _ => hfg ω']

/-- The total size as a range sum of `sizeN`. -/
theorem totalSize_eq_range (ω : C.Ω) :
    C.totalSize ω = ∑ i ∈ Finset.range C.m, C.sizeN i ω := by
  unfold ChunkSystemB.totalSize
  rw [← Fin.sum_univ_eq_sum_range (fun i => C.sizeN i ω) C.m]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold ChunkSystemB.sizeN
  rw [dif_pos i.isLt]

/-- `sizeN` congruence lifted to interval sums. -/
theorem sum_Ico_sizeN_congr {a b : ℕ} (hb : b ≤ C.m) {ω ω' : C.Ω}
    (hh : C.hist b ω' = C.hist b ω) :
    ∑ i ∈ Finset.Ico a b, C.sizeN i ω' = ∑ i ∈ Finset.Ico a b, C.sizeN i ω := by
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_Ico] at hi
  exact C.sizeN_congr (C.href i b (by omega) ω' ω hh)

/-- **CV from prophecy**: with a trivial initial history, total variance
at most `V`, and prophecy energy at most `PE`, the conditional
block-variance budget of the fixed-block partition is at most
`2·V + 2·PE`.  Each cell's conditional variance is its interval Doob
energy; each within-cell increment is the increment of the full total
minus the increment of the beyond-cell tail; the total's energy sums to
its variance, the tails' to the prophecy energy. -/
theorem cv_from_ppe {b M : ℕ} (hcov : C.m ≤ M * b)
    {V PE : ℝ}
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    (hVar : ∑ ω, C.P ω * (C.totalSize ω
      - ∑ ω', C.P ω' * C.totalSize ω') ^ 2 ≤ V)
    (hPPE : C.ProphecyBound PE) :
    ∑ k ∈ Finset.range M, ∑ ω, C.P ω
      * ((∑ i ∈ Finset.Ico (min (k * b) C.m) (min ((k + 1) * b) C.m),
            C.sizeN i ω)
        - C.condExp (fun ω' =>
            ∑ i ∈ Finset.Ico (min (k * b) C.m) (min ((k + 1) * b) C.m),
              C.sizeN i ω') (min (k * b) C.m) ω) ^ 2 ≤ 2 * V + 2 * PE := by
  set e : ℕ → ℕ := fun k => min (k * b) C.m with he_def
  have he0 : e 0 = 0 := by
    simp [he_def]
  have hemono : ∀ k, e k ≤ e (k + 1) := by
    intro k
    have h1 : k * b ≤ (k + 1) * b := Nat.mul_le_mul (by omega) le_rfl
    simp only [he_def]
    omega
  have heK : e M = C.m := by
    simp only [he_def]
    omega
  have hem : ∀ k, e k ≤ C.m := fun k => min_le_right _ _
  -- per cell: conditional variance = interval Doob energy
  have hcell : ∀ k, ∑ ω, C.P ω
      * ((∑ i ∈ Finset.Ico (e k) (e (k + 1)), C.sizeN i ω)
        - C.condExp (fun ω' =>
            ∑ i ∈ Finset.Ico (e k) (e (k + 1)), C.sizeN i ω') (e k) ω) ^ 2
      = ∑ h ∈ Finset.Ico (e k) (e (k + 1)), ∑ ω, C.P ω
          * (C.dinc (fun ω' =>
              ∑ i ∈ Finset.Ico (e k) (e (k + 1)), C.sizeN i ω') h ω) ^ 2 := by
    intro k
    exact interval_energy _ (hemono k)
      (fun ω ω' hh => sum_Ico_sizeN_congr (hem (k + 1)) hh)
  -- within a cell, the cell-mass increment is total minus tail
  have hdec : ∀ k, ∀ h ∈ Finset.Ico (e k) (e (k + 1)), ∀ ω : C.Ω,
      C.dinc (fun ω' =>
          ∑ i ∈ Finset.Ico (e k) (e (k + 1)), C.sizeN i ω') h ω
        = C.dinc C.totalSize h ω
          - C.dinc (C.tailSum (e (k + 1))) h ω
          - C.dinc (fun ω' =>
              ∑ i ∈ Finset.range (e k), C.sizeN i ω') h ω := by
    intro k h hm ω
    simp only [Finset.mem_Ico] at hm
    have hsplit : ∀ ω' : C.Ω, C.totalSize ω'
        = (∑ i ∈ Finset.range (e k), C.sizeN i ω')
          + ((∑ i ∈ Finset.Ico (e k) (e (k + 1)), C.sizeN i ω')
            + C.tailSum (e (k + 1)) ω') := by
      intro ω'
      rw [totalSize_eq_range]
      unfold ChunkSystemB.tailSum
      rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive (fun i => C.sizeN i ω')
          (Nat.zero_le (e k)) (le_trans (hemono k) (hem (k + 1))),
        ← Finset.sum_Ico_consecutive (fun i => C.sizeN i ω')
          (hemono k) (hem (k + 1)), ← Finset.range_eq_Ico]
    have h1 : C.dinc C.totalSize h ω
        = C.dinc (fun ω' => ∑ i ∈ Finset.range (e k), C.sizeN i ω') h ω
          + C.dinc (fun ω' =>
              (∑ i ∈ Finset.Ico (e k) (e (k + 1)), C.sizeN i ω')
                + C.tailSum (e (k + 1)) ω') h ω := by
      rw [← dinc_add]
      exact dinc_congr_fun hsplit h ω
    have h2 : C.dinc (fun ω' =>
          (∑ i ∈ Finset.Ico (e k) (e (k + 1)), C.sizeN i ω')
            + C.tailSum (e (k + 1)) ω') h ω
        = C.dinc (fun ω' =>
            ∑ i ∈ Finset.Ico (e k) (e (k + 1)), C.sizeN i ω') h ω
          + C.dinc (C.tailSum (e (k + 1))) h ω := dinc_add _ _ h ω
    rw [h2] at h1
    linarith
  -- prefix increments vanish inside the cell
  have hpre : ∀ k, ∀ h ∈ Finset.Ico (e k) (e (k + 1)), ∀ ω : C.Ω,
      C.dinc (fun ω' =>
          ∑ i ∈ Finset.range (e k), C.sizeN i ω') h ω = 0 := by
    intro k h hm ω
    simp only [Finset.mem_Ico] at hm
    refine dinc_of_meas hm.1 (fun ω ω' hh => ?_) ω
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    exact C.sizeN_congr (C.href i (e k) (by omega) ω' ω hh)
  -- pointwise square bound
  have hsq : ∀ k, ∀ h ∈ Finset.Ico (e k) (e (k + 1)), ∀ ω : C.Ω,
      (C.dinc (fun ω' =>
          ∑ i ∈ Finset.Ico (e k) (e (k + 1)), C.sizeN i ω') h ω) ^ 2
        ≤ 2 * (C.dinc C.totalSize h ω) ^ 2
          + 2 * (C.dinc (C.tailSum (e (k + 1))) h ω) ^ 2 := by
    intro k h hm ω
    rw [hdec k h hm ω, hpre k h hm ω]
    nlinarith [sq_nonneg (C.dinc C.totalSize h ω
      + C.dinc (C.tailSum (e (k + 1))) h ω)]
  -- total's Doob energy over the partition is its variance
  have henergy : ∑ k ∈ Finset.range M, ∑ h ∈ Finset.Ico (e k) (e (k + 1)),
      ∑ ω, C.P ω * (C.dinc C.totalSize h ω) ^ 2 ≤ V := by
    have hjoin : ∀ n : ℕ, ∑ k ∈ Finset.range n,
        ∑ h ∈ Finset.Ico (e k) (e (k + 1)),
          ∑ ω, C.P ω * (C.dinc C.totalSize h ω) ^ 2
        = ∑ h ∈ Finset.range (e n),
            ∑ ω, C.P ω * (C.dinc C.totalSize h ω) ^ 2 := by
      intro n
      induction n with
      | zero => simp [he0]
      | succ n ih =>
        rw [Finset.sum_range_succ, ih, Finset.range_eq_Ico,
          Finset.range_eq_Ico, Finset.sum_Ico_consecutive _
            (Nat.zero_le _) (hemono n)]
    rw [hjoin M, heK]
    have hivar : ∑ ω, C.P ω * (C.totalSize ω
        - C.condExp C.totalSize 0 ω) ^ 2
        = ∑ h ∈ Finset.Ico 0 C.m,
            ∑ ω, C.P ω * (C.dinc C.totalSize h ω) ^ 2 :=
      interval_energy C.totalSize (Nat.zero_le C.m)
        (fun ω ω' hh => by
          rw [totalSize_eq_range, totalSize_eq_range,
            Finset.range_eq_Ico]
          exact sum_Ico_sizeN_congr (le_refl C.m) hh)
    have hc0 : ∀ ω : C.Ω, C.condExp C.totalSize 0 ω
        = ∑ ω', C.P ω' * C.totalSize ω' := by
      intro ω
      have hatom : C.atom 0 ω = Finset.univ := by
        ext ω'
        simp only [C.mem_atom, Finset.mem_univ, iff_true]
        exact h0triv ω' ω
      unfold ChunkSystemB.condExp ChunkSystemB.mass
      rw [hatom, C.hPsum, div_one]
    rw [← Finset.range_eq_Ico] at hivar
    calc ∑ h ∈ Finset.range C.m,
          ∑ ω, C.P ω * (C.dinc C.totalSize h ω) ^ 2
        = ∑ ω, C.P ω * (C.totalSize ω - C.condExp C.totalSize 0 ω) ^ 2 :=
          hivar.symm
      _ = ∑ ω, C.P ω * (C.totalSize ω
            - ∑ ω', C.P ω' * C.totalSize ω') ^ 2 :=
          Finset.sum_congr rfl fun ω _ => by rw [hc0 ω]
      _ ≤ V := hVar
  -- prophecy over the partition
  have hproph := hPPE M e he0 hemono heK
  -- assemble
  calc ∑ k ∈ Finset.range M, ∑ ω, C.P ω
        * ((∑ i ∈ Finset.Ico (e k) (e (k + 1)), C.sizeN i ω)
          - C.condExp (fun ω' =>
              ∑ i ∈ Finset.Ico (e k) (e (k + 1)), C.sizeN i ω') (e k) ω) ^ 2
      = ∑ k ∈ Finset.range M, ∑ h ∈ Finset.Ico (e k) (e (k + 1)),
          ∑ ω, C.P ω * (C.dinc (fun ω' =>
            ∑ i ∈ Finset.Ico (e k) (e (k + 1)), C.sizeN i ω') h ω) ^ 2 :=
        Finset.sum_congr rfl fun k _ => hcell k
    _ ≤ ∑ k ∈ Finset.range M, ∑ h ∈ Finset.Ico (e k) (e (k + 1)),
          ∑ ω, C.P ω * (2 * (C.dinc C.totalSize h ω) ^ 2
            + 2 * (C.dinc (C.tailSum (e (k + 1))) h ω) ^ 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine Finset.sum_le_sum fun h hm => ?_
        refine Finset.sum_le_sum fun ω _ => ?_
        exact mul_le_mul_of_nonneg_left (hsq k h hm ω) (le_of_lt (C.hP ω))
    _ = 2 * (∑ k ∈ Finset.range M, ∑ h ∈ Finset.Ico (e k) (e (k + 1)),
          ∑ ω, C.P ω * (C.dinc C.totalSize h ω) ^ 2)
        + 2 * ∑ k ∈ Finset.range M, ∑ h ∈ Finset.Ico (e k) (e (k + 1)),
          ∑ ω, C.P ω * (C.dinc (C.tailSum (e (k + 1))) h ω) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ω _ => ?_
        ring
    _ ≤ 2 * V + 2 * PE := by
        have h1 := henergy
        have h2 := hproph
        nlinarith

end ChunkSystemB

end KServer


