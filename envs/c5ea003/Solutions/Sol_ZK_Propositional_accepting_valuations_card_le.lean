-- Prove2me | solution 1 for ZK.Propositional.accepting_valuations_card_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:54:27.063974+00:00
-- url     : https://prove2.me/submissions/f875363b-3348-48f7-889e-120712737b62

-- Sol generated from Cryptography/ZeroKnowledge/PropositionalTautology.lean
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_Graph3ColoringSimulator
import Definitions.Def_Cryptography_ZeroKnowledge_PropositionalTautology

/-!
# Zero-Knowledge Certification of Propositional Tautologies

This chapter isolates a finite theorem-proving protocol. A formula in `m` variables is
challenged at a uniformly chosen valuation. A false formula has at least one catching
valuation, so independent repetition gives an exact geometric soundness bound. Proof
values are committed with a uniformly masked element of a finite additive group; the
commitment distribution is independent of the value.

The construction deliberately separates two claims often conflated in informal
accounts. Random local checking supplies soundness, while zero knowledge requires an
independent simulation argument. Merely revealing a random proof line does not by
itself establish zero knowledge.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): Six falsifiable targets were ranked by expected impact.
(1, famous-open subtask) Polynomial-statement communication should suffice for every
Peano-arithmetic theorem. (2, famous-open subtask) a zero-knowledge proof system for
propositional validity with polynomial communication should illuminate the NP versus
coNP barrier. (3, famous-open subtask) PCP encodings of bounded arithmetic should
retain zero knowledge under local opening. (4, cross-domain) Boolean truth tables and
finite-product probability should give an exact repetition law. (5, cross-domain)
finite additive-group actions and transcript simulation should give perfect hiding.
(6, cross-domain) proof-spectrum locality and commitment locality should admit a
common sheaf-like gluing law. The experiment concentrated on targets (4) and (5),
the finite cores required before the three grander complexity claims can be assessed.

Experiment (Experimenter): Formulas were evaluated on all Boolean valuations. A
counterexample valuation was removed from the accepting set to obtain the sharp
`2^m-1` bound. Uniform additive masking was treated as a pushforward along a
translation bijection, producing an explicit simulator distribution.

Analysis (Analyst): The surviving soundness rate is `((2^m-1)/2^m)^k`, not `2^-k`.
Thus one random valuation per round becomes exponentially weaker as the number of
variables grows. By contrast, hiding is perfect and has no asymptotic loss.

Critique (Critic): Targets (1)--(3) do not follow from these arguments and remain
unsupported. The PCP theorem measures resources against an encoded instance and does
not erase the cost of an arbitrarily long derivation; moreover, opening a random raw
proof line neither verifies its dependencies nor hides its contents. The local-check
protocol here is not a polynomial-communication proof of arbitrary tautologies: its
challenge space is exponential and it assumes direct formula evaluation. Target (6)
needs a definition of compatible local transcript distributions before it is even a
well-posed theorem. Targets (4) and (5) survive. Their main bounds are non-vacuous and
depend on an explicit false valuation and independent-product reasoning.

Synthesis (Principal Investigator): The resulting theory cleanly bridges Boolean
algebra, finite combinatorics, probability, and additive cryptographic masking. It
also identifies the missing ingredient for succinct theorem certification: a
probabilistically checkable encoding with robust local inconsistency, rather than a
raw list of derivation steps.
-- !-- Lab Notes -- !--
-/

open ZK.Propositional




/-- Failure of tautologicity is witnessed by a concrete rejecting valuation. -/
theorem exists_rejecting_valuation {m : ℕ} {p : Formula m}
    (h : ¬ p.IsTautology) : ∃ v : Fin m → Bool, p.eval v = false := by
  classical
  unfold Formula.IsTautology at h
  push_neg at h
  obtain ⟨v, hv⟩ := h
  refine ⟨v, ?_⟩
  cases he : p.eval v with
  | false => rfl
  | true => exact False.elim (hv he)




variable {q : ℕ} [NeZero q]








open ZK.Propositional in
theorem solution{m : ℕ} (p : Formula m)
    (h : ¬ p.IsTautology) :
    (Finset.univ.filter (fun v : Fin m → Bool => p.eval v = true)).card ≤ 2 ^ m - 1 := by
  classical
  obtain ⟨v₀, hv₀⟩ := exists_rejecting_valuation h
  have hsub : (Finset.univ.filter (fun v : Fin m → Bool => p.eval v = true)) ⊆
      Finset.univ.erase v₀ := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    rintro rfl
    rw [hv₀] at hv
    simp at hv
  calc
    (Finset.univ.filter (fun v : Fin m → Bool => p.eval v = true)).card
        ≤ (Finset.univ.erase v₀).card := Finset.card_le_card hsub
    _ = Fintype.card (Fin m → Bool) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v₀), Finset.card_univ]
    _ = 2 ^ m - 1 := by simp
