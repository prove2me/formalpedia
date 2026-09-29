-- Prove2me | solution 1 for VoiceLeading.voiceLeading_cost_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T21:59:59.42561+00:00
-- url     : https://prove2.me/submissions/0e876a10-4228-4ea6-bc92-2f921add9f88

import Mathlib
import Definitions.Def_Bridges_VoiceLeadingCategory
open VoiceLeading in
theorem solution {n : ℕ} {V W U : Voicing n} (f : VL n V W) (g : VL n W U) :
    (f.comp g).cost ≤ f.cost + g.cost := by
  unfold VL.cost VL.comp
  -- voice by voice, `|V i - U(g(f i))| ≤ |V i - W(f i)| + |W(f i) - U(g(f i))|`
  calc ∑ i : Fin n, |(V i : ℝ) - (U ((f.perm.trans g.perm) i) : ℝ)|
      ≤ ∑ i : Fin n, (|(V i : ℝ) - (W (f.perm i) : ℝ)| + |(W (f.perm i) : ℝ) - (U (g.perm (f.perm i)) : ℝ)|) := by
        apply Finset.sum_le_sum
        intro i _
        exact abs_sub_le _ _ _
    _ = ∑ i : Fin n, |(V i : ℝ) - (W (f.perm i) : ℝ)| + ∑ j : Fin n, |(W j : ℝ) - (U (g.perm j) : ℝ)| := by
        rw [Finset.sum_add_distrib]
        congr 1
        -- reindex the second sum by `j = f i`
        exact Equiv.sum_comp f.perm (fun j => |(W j : ℝ) - (U (g.perm j) : ℝ)|)
