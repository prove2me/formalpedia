-- Prove2me | Theorems.Thm_KServer_gamPot_corner_dispatch
-- name    : KServer.gamPot_corner_dispatch
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T18:47:51.961344+00:00
-- url     : https://prove2.me/theorems/fd584fe6-f2c0-4f89-b9c9-69b91542572e
-- title:
--   The corner case analysis for the auxiliary potential Gamma
-- statement:
--   Let $x, z, y, t$ be four points of a metric space, thought of as the corners of a rectangle listed clockwise, so that $\{x,y\}$ and $\{z,t\}$ are its diagonals. Suppose the last request $r$ and two further points $p$ and $q$ each lie on **both** diagonals. Then, whenever $b, b', f$ are among the four corners and $\{d,d'\}$ is one of the two diagonals, the corresponding instance of the second auxiliary potential is dominated by the lazy potential:
--
--   $$\bigl(-rp + pb + pb' - w(b,b')\bigr) + rq + \bigl(dd' - w(q,d) - w(q,d')\bigr) + \bigl(qf - w(p,f)\bigr) \;\le\; \Psi_{w,r}.$$
--
--   ## Role
--
--   This is the combinatorial core of the proof that $\Gamma_{w,r} \le \Psi_{w,r}$ in the city-block plane, isolated from the geometry, and the counterpart for $\Gamma$ of the corresponding statement for $\Lambda$. The plane is used only to produce the rectangle and to push the free points out to its corners; what remains holds in **any** metric space with four points and three further points placed as described.
--
--   Note that $r$ itself is required to lie on both diagonals, which is not needed in the analysis of $\Lambda$. It is what makes the case "$b$ and $b'$ in opposite corners" work: there the sum $pb + pb'$ collapses to $bb'$, and the bound has to reconstitute $bb'$ as $rb + rb'$.
--
--   The proof is the exhaustive case analysis over the $4^3$ assignments of corners to $b, b', f$ and the four choices of diagonal for $(d,d')$ — 256 configurations, each settled by one of the eight configuration lemmas. The case $b = b'$ is preceded by the reduction that moves $p$ out to the corner opposite $b$; only after that move do the remaining configurations apply.
--
--   **Formalization note.** Each case is reached after at most one interchange of $b$ with $b'$ and one of $d$ with $d'$, both of which are identities for the expression — the first from the invariance of the work function under permuting a configuration, the second from the symmetry of the distance. The betweenness hypotheses that the configuration lemmas require are, in each case, one of sixteen instances of the six displayed diagonal identities, established once before the split.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Lemma 6, the case analysis following formula (8): 'we can assume that b, b', f, d, d' are in {x, y, z, t} and {d,d'} = {x,y} or {z,t}.'

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem gamPot_corner_dispatch (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r x z y t p q : M)
    (hp1 : dist x p + dist p y = dist x y) (hp2 : dist z p + dist p t = dist z t)
    (hq1 : dist x q + dist q y = dist x y) (hq2 : dist z q + dist q t = dist z t)
    (hr1 : dist x r + dist r y = dist x y) (hr2 : dist z r + dist r t = dist z t)
    (B B' F D D' : M)
    (hB : B = x ∨ B = z ∨ B = y ∨ B = t)
    (hB' : B' = x ∨ B' = z ∨ B' = y ∨ B' = t)
    (hF : F = x ∨ F = z ∨ F = y ∨ F = t)
    (hDD : (D = x ∧ D' = y) ∨ (D = z ∧ D' = t) ∨ (D = y ∧ D' = x) ∨ (D = t ∧ D' = z)) :
    (-dist r p + (dist p B + dist p B' - workFnU C₀ σ ![r, B, B']))
      + dist r q + dist D D' - workFnU C₀ σ ![r, q, D] - workFnU C₀ σ ![r, q, D']
      + dist q F - workFnU C₀ σ ![r, p, F]
      ≤ lazyPot C₀ σ r := by sorry

end KServer
