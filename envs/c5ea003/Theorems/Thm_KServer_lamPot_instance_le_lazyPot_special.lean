-- Prove2me | Theorems.Thm_KServer_lamPot_instance_le_lazyPot_special
-- name    : KServer.lamPot_instance_le_lazyPot_special
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T17:40:37.075867+00:00
-- url     : https://prove2.me/theorems/981d0f0c-3893-409c-a7ce-b83fa63e97da
-- title:
--   Three configurations in which an instance of Lambda is below the lazy potential
-- statement:
--   In an **arbitrary** metric space, an instance of the auxiliary potential $\Lambda_{w,r}$ is bounded by the lazy potential $\Psi_{w,r}$ in each of the following three configurations of its witnesses:
--
--   1. $p$ lies on a geodesic between $b$ and $b'$, that is $pb + pb' = bb'$;
--   2. $b = b'$ and $c = b$;
--   3. $b = b'$ and $p$ lies on a geodesic between $c$ and $b$.
--
--   In each case the remaining witnesses are entirely unconstrained.
--
--   ## Role
--
--   The comparison $\Lambda_{w,r} \le \Psi_{w,r}$ is what makes the Work Function Algorithm $3$-competitive in the city-block plane, and it is proved there by pushing every free point of $\Lambda$ out to a corner of a bounding rectangle and then examining which points land in which corners. What the three statements above record is that a large part of that case analysis needs no plane at all: the geometry enters only through the *betweenness* relations that the rectangle supplies, and once those are assumed, the argument is the usual mixture of the triangle inequality, the Lipschitz property and quasiconvexity, valid in any metric space.
--
--   Concretely, in the plane the first case is what happens when $b$ and $b'$ land in opposite corners — every point of the rectangle lies on the diagonal — while the second and third are the cases where $b$ and $b'$ land in the *same* corner, split according to whether $c$ lands there too or in the opposite corner.
--
--   It is worth noting that in the first case the appeal to quasiconvexity produces two branches which are usually handled by a symmetry argument, but here both branches lead to the *same* final instance of $\Psi_{w,r}$, so no symmetry is needed.
--
--   **Formalization note.** Each of the three parts is a single linear-arithmetic combination of: one instance of $\Psi_{w,r}$ at explicitly chosen witnesses, two or three triangle inequalities, one application of the Lipschitz property in pinned two-point form, and one application of pairwise quasiconvexity (whose `min` is split, with both branches closing identically). The symmetry $w(x,y) = w(y,x)$ of the work function on the last two coordinates is supplied where the chosen instance and the hypotheses disagree on the order.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Lemma 5, Cases 1, 2.1 and 2.2.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem lamPot_instance_le_lazyPot_special (M : Type) [MetricSpace M] (C₀ : Config 3 M)
    (σ : List M) (r : M) :
    (∀ p q b b' c c' e e' : M, dist p b + dist p b' = dist b b' →
      (-dist r p + (dist p b + dist p b' - workFnU C₀ σ ![r, b, b']))
        + (-dist r q + (dist q c + dist q c' - workFnU C₀ σ ![r, c, c']))
        - workFnU C₀ σ ![r, p, q] + dist e e' - workFnU C₀ σ ![r, e, e']
        ≤ lazyPot C₀ σ r)
    ∧ (∀ p q b c' e e' : M,
      (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
        + (-dist r q + (dist q b + dist q c' - workFnU C₀ σ ![r, b, c']))
        - workFnU C₀ σ ![r, p, q] + dist e e' - workFnU C₀ σ ![r, e, e']
        ≤ lazyPot C₀ σ r)
    ∧ (∀ p q b c c' e e' : M, dist p c + dist p b = dist c b →
      (-dist r p + (dist p b + dist p b - workFnU C₀ σ ![r, b, b]))
        + (-dist r q + (dist q c + dist q c' - workFnU C₀ σ ![r, c, c']))
        - workFnU C₀ σ ![r, p, q] + dist e e' - workFnU C₀ σ ![r, e, e']
        ≤ lazyPot C₀ σ r) := by sorry

end KServer
