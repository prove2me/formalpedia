-- Prove2me | Theorems.Thm_KServer_chunk_combining_zero_floor
-- name    : KServer.chunk_combining_zero_floor
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-07T23:20:28.391713+00:00
-- url     : https://prove2.me/theorems/b6cb44c7-3fde-486c-a792-d77921b94800
-- title:
--   Regrouping a chunk system with size floor zero, under a Doob jump bound
-- statement:
--   Let $C$ be a chunk system with online escapes on a metric space with marked points $s,t$: a random sequence of chunks of set requests with adapted sizes $c_j$, a filtration $(\mathcal F_h)$, and the conditional cost bound against every evader and every online escape rule at escape price $p_e$. Suppose its sizes lie in $[0,c_B]$, its initial information is trivial, no chunk is the empty request list, and the Doob martingale $D_h=\mathbb E[\sum_j c_j\mid\mathcal F_h]$ of its total has the pointwise jump bound $|D_{h+1}-D_h|\le jb$.
--
--   **Statement.** Write $\mu=\mathbb E[\sum_j c_j]/M$ for the target chunk mass. For every $M\ge1$ and every window $[c_{\mathrm{Lo}}',c_{\mathrm{Hi}}']$ with
--   $$0<c_{\mathrm{Lo}}'\le \mu-(c_B+jb),\qquad \mu+(c_B+jb)\le c_{\mathrm{Hi}}',$$
--   and every escape price $p'\ge p_e+\mu+c_B+jb$, the chunks of $C$ can be regrouped into a chunk system with **exactly $M$ chunks**, all of whose sizes lie in $[c_{\mathrm{Lo}}',c_{\mathrm{Hi}}']$, with the same expected total, escape price $p'$, trivial initial information and no empty chunk.
--
--   **This is the regrouping step the recursion actually needs.** The platform already has `KServer.chunk_combining_strong`, which is this statement with a *positive* size floor $c_A>0$ on the input, plus $jb\le c_A$. But the level steps `KServer.level_step_sturdy` and `KServer.level_step_full` both take and return systems with size floor $0$: the race construction produces chunks of size zero, and no combinator can raise a floor, since `KServer.ChunkSystemB.adjust` only lowers one. So the output of a level step can never be handed to `chunk_combining_strong`, and the induction of BCR's Lemma 12 cannot get from one level to the next. The floor-zero case stated here closes that gap.
--
--   **Why the jump bound is the right hypothesis.** The regrouping cuts at the stopping times $h_i=\min\{h: F_h\le F_0-i\mu\}$, where $F_h=\mathbb E[\sum_{j\ge h}c_j\mid\mathcal F_h]$, and the pointwise size window of the output requires that $F$ undershoot its threshold by a controlled amount, that is, that $F$ decrease slowly along every branch. By `KServer.slow_decrement_of_doob_jump` a pointwise Doob jump bound gives exactly that, with parameter $c_B+jb$, which is the half-width appearing above; the sizes being adapted, one revealed chunk moves the remaining mass by its own size plus one jump of the Doob martingale.
--
--   This is the hypothesis a randomized construction can meet. The alternative repair on the platform, `KServer.chunk_regroup_stable`, additionally assumes bounded surprise, and that assumption is unusable here: by `KServer.bounded_surprise_total_le` it forces the total of every branch to lie within one chunk of the mean, whereas the total produced by a level step fluctuates by the anti-concentration gain of the race, which is many chunks.
--
--   **Formalization note.** The size floor of the input is literally $0$ rather than a variable $c_A$, since that is the shape the level steps produce. The three structural clauses of the conclusion are the ones the next level step consumes: the exact chunk count, the trivial initial history, and the nonemptiness of the chunks.
--
--   **A warning for a prover, from an attempt to transfer the positive-floor proof.** The existing proof of `KServer.chunk_combining_strong` uses the size floor in two places, and only one of them is cosmetic.
--
--   The cosmetic use is positivity of the expected total, which the floor supplies through `expTotal_pos`; at floor zero the sizes are still nonnegative, so the expected total is nonnegative, and every consequence drawn from it (nonnegativity, monotonicity and the upper bound of the target levels, and hence monotonicity of the stopping times) survives unchanged. Two further steps need small rewrites but no new hypothesis: the strict increase of the stopping times follows from the slack $c_B+jb<\mu$ alone, since every time before $\tau_i$ has conditional future mass above $\mathrm{lvl}_i$ and the value at $\tau_i$ itself is at least $\mathrm{lvl}_i-(c_B+jb)>\mathrm{lvl}_{i+1}$; and the last boundary must be pinned to the final chunk by definition rather than derived, because at floor zero the conditional future mass can reach zero early, and the last window then has conditional size in $[\mu-(c_B+jb),\mu]$, still inside the window.
--
--   The substantive use is in the escape-price charging. That argument bounds the conditional future mass at the moment the escape rule fires by its value at the start of the window, which is antitonicity of the conditional future mass; and antitonicity holds exactly in the descending regime $jb\le c_{\mathrm{Lo}}$, which floor zero destroys. Without it the conditional future mass can rise inside a window, by up to one Doob jump per chunk, and a window at floor zero can be long. Enlarging the reserve to absorb that drift is not an option in the intended application: the drift bound would be of the order of the number of chunks times the jump, which exceeds the distance between the marked points.
--
--   The route that should work is the paper's own charging, which never evaluates the conditional future mass at the firing time. Bubeck, Coester and Rabani charge the escape price to the subchunk during which the algorithm escapes and a fake cost $\mathbb E[\tilde c_j\mid\tilde\rho_{\le h_{i-1}}]$, conditioned at the *window start*, to each subsequent subchunk; the total so charged is at most $p_{\mathrm{esc}}+c_i$, and the bound on $c_i$ is the window's own size bound, already available. So the charging step should be re-derived over conditional masses at the window start rather than transferred from the positive-floor proof.
--
--   **Status: reduced to one inequality, machine-checked.** The conditional form `KServer.chunk_combining_zero_floor_antitone` is now proved: it is this statement with the extra hypothesis that the conditional future mass $F_h$ is non-increasing along every branch. Its proof carries the whole positive-floor development to floor zero, and the extra hypothesis is consumed in exactly one step, the comparison of $F$ at the position where the escape rule fires with its value at the start of the window. So what remains here is precisely to remove that hypothesis, by replacing the charging step with the source's version, which conditions at the window start throughout and never evaluates $F$ at the firing position.
--
--   **The argument that removes it.** The obstruction is only in the bookkeeping. The existing induction carries *realized* window masses, so at the position where the escape fires it must bound the expected remaining mass conditioned on the branches that escaped there, and conditioning on that sub-event is what forces a comparison of $F$ at two different times. The source instead charges quantities that are **measurable at the window start**: the escape price $p_e$ to the subchunk during which the algorithm escapes, and a fake cost $\mathbb E[\tilde c_j\mid\mathcal F_a]$ to every later subchunk of that window, where $a$ is the window start.
--
--   Those fake charges are constants on the atom of $\mathcal F_a$, so for every branch, whatever the escape position $j^\ast$ happens to be there,
--   $$p_e+\sum_{j>j^\ast}\mathbb E[\tilde c_j\mid\mathcal F_a]\;\le\;p_e+\sum_{j\ \text{in the window}}\mathbb E[\tilde c_j\mid\mathcal F_a]\;=\;p_e+c_i\;\le\;p',$$
--   the middle step discarding nonnegative terms. The bound is therefore *pointwise in the branch*, and no sub-event is ever conditioned on. Summing over the atom, the branches that did not escape are handled by the input system's own conditional cost bound as before, and the two together give $c_i\cdot\mathrm{mass}\le\sum_\omega P(\omega)\,\mathrm{bailcost}(\omega)$.
--
--   So the remaining task is to restate the charging induction with the post-escape part carried as window-start conditional sizes rather than realized masses. Everything else in the development is already floor-zero clean.
--
--   **Correction to the paragraph above, and a warning that this statement may need amending.** Working the window-start charging through to the end, it does not close as stated, and the reason is instructive.
--
--   The accounting compares, subchunk by subchunk, what the algorithm is credited with against the size it must cover. On the branches where the escape rule has not yet fired, the input system's own conditional cost bound applies at $\mathcal F_j$, because "has not fired by $j$" is decided by the history before $j$. On the branches where it has fired, the algorithm is credited with the fake charge. For the comparison to survive taking expectations one needs
--   $$\mathbb E\bigl[\tilde c_j\,\mathbf 1[\text{fired by }j]\ \bigm|\ \mathcal F_a\bigr]\;\le\;\mathbb E[\tilde c_j\mid\mathcal F_a]\cdot\Pr[\text{fired by }j\mid\mathcal F_a],$$
--   that is, the sizes must be uncorrelated with the escape event given the information at the window start. Nothing supplies that. Conditioning the fake charge at $\mathcal F_{j-1}$ instead makes the step correct, since the escape event is decided by then, but the sizes are predictable, so the charge becomes the realized size and the total charged over a window is the realized window mass, which at floor zero is not bounded by the window's conditional size.
--
--   This is the same conditioning subtlety that already refuted the metric-space-independent form of the regrouping step, `KServer.bcr_lemma15_regroup`, and it says the size floor is doing real work in the escape-price accounting rather than only in the bookkeeping: with a positive floor and $jb\le c_A$, the conditional remaining mass at the firing position is bounded by a window's worth *on the sub-event where the rule fired*, because it is measured on that sub-event, and this is exactly what the escape price has to cover.
--
--   So a prover should expect to need one more hypothesis, controlling how far the conditional remaining mass can rise inside a window — a bound on the window length, or directly on the upward drift of $F$ — and the statement here should be amended to carry it once its right form is known. The conditional version `KServer.chunk_combining_zero_floor_antitone` remains correct and proved; the hypothesis it carries is the strongest such control, and the open question is how much of it can be given up.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The randomized k-server conjecture is false!, STOC 2023, https://arxiv.org/abs/2211.05753, Lemma 15 (pp. 19-21). Floor-zero form of the platform theorem KServer.chunk_combining_strong, which is the case needed because KServer.level_step_sturdy and KServer.level_step_full produce systems with size floor 0.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond

namespace KServer

theorem chunk_combining_zero_floor {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t 0 cB T pe mL)
    (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    (hch : ∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ [])
    {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hcB : 0 ≤ cB)
    {M : ℕ} (hM0 : 0 < M) {cLo' cHi' p' : ℝ}
    (hlo0 : 0 < cLo')
    (hlo : cLo' ≤ (∑ ω, C.P ω * ∑ i, C.size ω i) / M - (cB + jbS))
    (hhi : (∑ ω, C.P ω * ∑ i, C.size ω i) / M + (cB + jbS) ≤ cHi')
    (hp : pe + ((∑ ω, C.P ω * ∑ i, C.size ω i) / M + (cB + jbS)) ≤ p') :
    ∃ C' : ChunkSystemB X s t cLo' cHi' T p' M,
      C'.m = M ∧ (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) := by sorry

end KServer
