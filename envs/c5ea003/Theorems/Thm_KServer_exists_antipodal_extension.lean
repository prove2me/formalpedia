-- Prove2me | Theorems.Thm_KServer_exists_antipodal_extension
-- name    : KServer.exists_antipodal_extension
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T19:41:46.130374+00:00
-- url     : https://prove2.me/theorems/c55fa746-8e56-49ca-910e-15b9bdb95d2a
-- title:
--   Every metric space extends to one in which every point has an antipode
-- statement:
--   A point $\bar p$ of a metric space is the **antipode** of $p$ if every point lies on a geodesic between them:
--   $$px + x\bar p = p\bar p \qquad\text{for all } x .$$
--   Most spaces have no antipodes — the line and the tree have none — but every metric space of finite diameter $\Delta$ can be extended so that every point acquires one. Adjoin a second copy $\bar M$ of the space and set
--   $$\bar p\,\bar q = pq, \qquad \bar p q = 2\Delta - pq .$$
--   The result is again a metric space, of diameter $2\Delta$, containing $M$ isometrically, and in it $p$ and $\bar p$ are antipodes of each other, at distance exactly $2\Delta$.
--
--   ## Role
--
--   This construction is what makes the Coester–Koutsoupias potential expressible. Their unifying potential for the $k$-server problem is
--   $$\Phi_{x_1 \dots x_k}(w) \;=\; \sum_{i=0}^{k} w\bigl(\bar x_i^{\,i}\, x_{i+1} \dots x_k\bigr),$$
--   a sum of $k+1$ work-function values in which the $i$-th term places $i$ servers at the antipode of $x_i$; the potential itself is the minimum over the choice of $x_1, \dots, x_k$. Antipodes are the device by which the "lazy adversary" of Chrobak and Larmore — an adversary that commits to a configuration and then requests only its own points — is expressed as a closed formula rather than as a limit of long request sequences. The construction is harmless because the work function of the extended space restricts to the original one on configurations of original points.
--
--   The verification is a case analysis on which copies the points lie in. The one case with content is a distance between two original points bounded by a detour through a copy: there both legs cost at least $\Delta$, so the detour costs at least $2\Delta$, which already exceeds the diameter. The antipode identity itself is immediate: whichever copy $x$ lies in, one of the two legs is $pq$ and the other is $2\Delta - pq$.
--
--   **Formalization note.** The extension is realised on the sum type $M \oplus M$, with the antipode map being the exchange of the two summands, so that it is an involution by construction. The hypothesis $\Delta > 0$ is what makes the result a metric rather than a pseudometric: it is what separates a point from the copy of itself, at distance $2\Delta$. The distance function is exhibited explicitly rather than installed as an instance, so that the statement quantifies over its properties directly.
-- source:
--   C. Coester, E. Koutsoupias, Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle, ICALP 2021, arXiv:2102.10474, Section 3.2: 'As mentioned in [Koutsoupias99], every metric space can be extended so that every point has an antipode: To achieve this, we add to M another copy of the same points, and define distances by bar-p bar-q = pq and bar-p q = 2*Delta - pq. It is easy to check that M union bar-M is still a metric space (of diameter 2*Delta) where bar-p and p are antipodes of each other.'

import Mathlib

namespace KServer

theorem exists_antipodal_extension (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ x y : M, dist x y ≤ Δ) :
    ∃ D : (M ⊕ M) → (M ⊕ M) → ℝ,
      (∀ p, D p p = 0)
      ∧ (∀ p q, D p q = D q p)
      ∧ (∀ p q r, D p r ≤ D p q + D q r)
      ∧ (∀ p q, D p q = 0 → p = q)
      ∧ (∀ x y : M, D (Sum.inl x) (Sum.inl y) = dist x y)
      ∧ (∀ p q : M ⊕ M, D p q + D q (Sum.swap p) = 2 * Δ) := by sorry

end KServer
