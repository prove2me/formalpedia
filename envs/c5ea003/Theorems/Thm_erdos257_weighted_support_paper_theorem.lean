-- Prove2me | Theorems.Thm_erdos257_weighted_support_paper_theorem
-- name    : erdos257_weighted_support_paper_theorem
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T02:17:08.842237+00:00
-- url     : https://prove2.me/theorems/f6d332dc-466f-4f2a-a207-6b0455c0fbbd
-- title:
--   Weighted support theorem for reciprocal Mersenne subseries (Erdős #257)
-- statement:
--   For every integer base b at least two and every infinite positive-integer host H with a finite nonempty prime set witnessing finite b-weighted mass, the reciprocal Mersenne subseries on every infinite subset A of H is irrational at b. If H instead has such a witness for base two, every infinite subset A has an irrational subseries at every integer base b at least two. The host witness is chosen before the subset and base in the second clause. Taking A = H recovers the two direct assertions of Theorem 1.
--
--   **Where to inspect the proof.** The `:= by sorry` on this page is Prove2Me’s challenge placeholder, not the accepted proof. The accepted Solution is stored separately under **View graph → Solutions & Sketches**; the graph route currently asks signed-out readers to sign in. The [public proof packet](https://github.com/wcook04/plectis-erdos/blob/1bbf4c21c22bc55c4502a43178586147e30b3a44/docs/research-commons/PROVE2ME_WEIGHTED_257_PACKET.md) prints the byte-exact accepted wrapper Solution for signed-out inspection and distinguishes it from the older offline adapter. The [changed-hypothesis exercise](https://github.com/wcook04/plectis-erdos/blob/7e33a58bb86180013b1fb855cdd8aaff1d7f9057/docs/research-commons/PROVE2ME_WEIGHTED_257_PACKET.md#try-changing-a-hypothesis) asks when the weighted certificate survives a change of base or support growth. Its parameterised family is an ordinary deduction from the paper, not a separately proved Lean instance. The proof combines the linked fixed-base hereditary and all-base weighted results in the same pinned Lean environment. The [pinned public Lean source](https://github.com/wcook04/plectis-erdos-lean/tree/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8) contains those components; this wrapper is a composition, not a source declaration. A [proved finite-deletion consequence](https://prove2.me/theorems/617fa7c2-841e-4ab0-9f2c-7152d79e3891) uses the main theorem. A [stronger eventual-containment consequence](https://prove2.me/theorems/f64da58c-9d9e-4d42-bff7-0907905e6ac5) combines it with the [finite-prefix transfer](https://prove2.me/theorems/26a05c39-b6fa-47d2-9e35-5a39a8185a03): an infinite support may contain finitely many exponents outside a binary-weighted host. The assertion for every infinite support remains open.
-- source:
--   Reviewed composition of two accepted Lean results formalizing Will Cook’s Theorem 1, not a source declaration: https://prove2.me/theorems/27568cbc-77aa-49d2-bc80-69741ac3d5ba and https://prove2.me/theorems/521ada00-9a14-401d-aec5-134bd5c106b7 . Pinned Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/tree/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8 . Paper by Will Cook (CC-BY-4.0), Theorem 1: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L54-L75 . The paper separately credits Erdős’s earlier criterion and discloses substantial AI-assisted research and drafting: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188 .

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_AnalyticTargets
import Mathlib

theorem erdos257_weighted_support_paper_theorem :
    (∀ (b : ℕ) (H : Set ℕ), 2 ≤ b → 0 ∉ H → H.Infinite →
      ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted b H →
      ∀ A : Set ℕ, A ⊆ H → A.Infinite →
        Irrational (Erdos249257.erdosSupportSeries b A)) ∧
    (∀ H : Set ℕ, 0 ∉ H → H.Infinite →
      ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted 2 H →
      ∀ A : Set ℕ, A ⊆ H → A.Infinite →
        ∀ b : ℕ, 2 ≤ b →
          Irrational (Erdos249257.erdosSupportSeries b A)) := by sorry
