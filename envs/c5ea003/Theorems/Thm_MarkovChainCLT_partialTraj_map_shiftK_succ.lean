-- Prove2me | Theorems.Thm_MarkovChainCLT_partialTraj_map_shiftK_succ
-- name    : MarkovChainCLT.partialTraj_map_shiftK_succ
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T20:35:05.027833+00:00
-- url     : https://prove2.me/theorems/1e608d50-05f7-493d-9ec2-8beee0eb02f8
-- title:
--   Time-homogeneity at an arbitrary offset: the $k$-shift commutes with one-step extension
-- statement:
--   Let $P$ be a Markov kernel on $\mathsf{X}$, and write $\sigma^k$ for the shift that drops the first $k$ coordinates of a partial trajectory, $(\sigma^k v)_i = v_{k+i}$. Then for all $k, m$ and every partial trajectory $v = (v_0,\dots,v_{k+m})$,
--
--   $$\sigma^k_*\bigl[\mathrm{partialTraj}(k{+}m,\,k{+}m{+}1)(v)\bigr] \;=\; \mathrm{partialTraj}(m,\,m{+}1)\bigl(\sigma^k v\bigr).$$
--
--   **What it says.** Extending a trajectory by one step and then dropping its first $k$ coordinates is the same as dropping the first $k$ coordinates and then extending. This is the arbitrary-offset form of time-homogeneity; the case $k = 1$ is the basic statement that the shift commutes with one-step extension.
--
--   **Why the offset version is needed separately.** The $k=1$ case suffices to prove that the law of the *whole* trajectory started at a point is shift-covariant, and hence that a chain started from an invariant measure is stationary. It does **not** suffice for the conditional statements that quantitative mixing estimates require: bounding the dependence between $\sigma(X_0,\dots,X_j)$ and $\sigma(X_{j+n}, X_{j+n+1},\dots)$ means comparing a trajectory *conditioned on its first $j{+}1$ coordinates* with a chain restarted $n$ steps later, and that comparison is indexed by two independent offsets. Iterating the $k=1$ lemma cannot be done painlessly either, because the natural composition identity $\sigma^{k+1} = \sigma^k \circ \sigma$ forces the index arithmetic $(m{+}1)+k$ versus $(m{+}k)+1$, which is not definitional in $\mathbb{N}$ — addition recurses on its second argument. Writing the total length as $k+m$ from the outset, as here, makes $k+(m{+}1)$ and $(k{+}m)+1$ definitionally equal and the induction goes through without transport.
--
--   **Two facts consumed, exactly as in the unit-offset case.** The left side extends using the kernel $P(v_{k+m},\cdot)$ and the right side using $P\bigl((\sigma^k v)_m,\cdot\bigr)$; these agree because $(\sigma^k v)_m = v_{k+m}$ — the shift preserves the *last* coordinate, which is all the transition law depends on (the Markov property) — and because the kernel is the same $P$ at both times (time-homogeneity). For a genuinely time-inhomogeneous family the statement is false.
--
--   **Proof.** Rewrite both sides with the explicit pushforward description of a one-step extension, so each is a pushforward of the single measure $P(v_{k+m},\cdot)$ along a gluing map. After identifying the kernels, the claim reduces to a pointwise identity between the two gluing maps, settled by splitting on whether the index $i$ satisfies $i \le m$: the two branch conditions $k+i \le k+m$ and $i \le m$ are equivalent by cancellation, the first branch returns $v_{k+i}$ on both sides, and the second returns the newly drawn coordinate on both sides.
-- source:
--   C. T. Ionescu Tulcea, "Mesures dans les espaces produits", Atti Accad. Naz. Lincei Rend. 7 (1949) 208-211; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 3; C. J. Geyer, "Practical Markov Chain Monte Carlo", Statistical Science 7 (1992) 473-483, Section 3.

import Definitions.Def_MarkovChainPathMeasure

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.partialTraj_map_shiftK_succ {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (k m : ℕ) (v : Π _i : Finset.Iic (k + m), S) :
    (Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P)
        (k + m) (k + m + 1) v).map
        (fun u i => u ⟨k + i.1,
          Finset.mem_Iic.2 (Nat.add_le_add_left (Finset.mem_Iic.mp i.2) k)⟩)
      = Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P) m (m + 1)
          (fun i => v ⟨k + i.1,
            Finset.mem_Iic.2 (Nat.add_le_add_left (Finset.mem_Iic.mp i.2) k)⟩) := by sorry
