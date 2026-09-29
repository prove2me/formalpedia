-- Prove2me | Theorems.Thm_Novelty_NoPinning_card_factor_pairs
-- name    : Novelty.NoPinning.card_factor_pairs
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:15:09.878519+00:00
-- url     : https://prove2.me/theorems/36e0435c-fc4d-4526-86ce-b1865b62ca29
-- title:
--   Perfect uniformity.
-- statement:
--   **Perfect uniformity.**  In a finite group every element has exactly `|G|`
--   ordered factorisations.
--
--   ```lean
--   theorem Novelty.NoPinning.card_factor_pairs[Fintype G] [DecidableEq G] (u : G) :
--       (Finset.univ.filter (fun p : G × G => p.1 * p.2 = u)).card = Fintype.card G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/NoPinningUniformity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/NoPinningUniformity.lean#L46

-- Thm stub generated from Novelty/NoPinningUniformity.lean
import Mathlib
import Definitions.Def_Novelty_NoPinningLemma
/-
# Perfect uniformity of the product map: the information-theoretic core

Fifth companion to `Novelty/NoPinningLemma.lean`.  The no-pinning lemma is
analytic (Dirichlet).  Underneath it lies a purely group-theoretic fact which
explains *why* no congruence battery can ever leak a factor: the multiplication
map of a group is a perfectly uniform hash.  Every value `u` has exactly `|G|`
ordered factorisations `u = x·y`, and the first coordinate ranges over the whole
group.  Observing the product therefore conveys **zero** information about the
individual factor class.

## Main results

* `factorPairEquiv` — for any group `G` and any `u : G`, the set of ordered
  factorisations `{(x,y) : x·y = u}` is in bijection with `G` itself.
* `card_factor_pairs` — the finite count: `|{(x,y) : x·y = u}| = |G|`,
  independent of `u`.
* `card_factor_pairs_zmod` — for the unit group of `ZMod L` this is Euler's
  `φ(L)`: given the residue of a semiprime mod `L`, exactly `φ(L)` factor
  classes remain, i.e. all of them.
* `existsUnique_partner` — each candidate class has exactly one partner class
  (the analytic content of `compensating_class_unique`, at group level).
* `consistent_class_count_independent_of_target` — the number of consistent
  candidate classes does not depend on the observed data: a modulus-`L` battery
  transmits no information about the factor class.
-/


open Novelty.NoPinning

variable {G : Type} [Group G]

theorem Novelty.NoPinning.card_factor_pairs[Fintype G] [DecidableEq G] (u : G) :
    (Finset.univ.filter (fun p : G × G => p.1 * p.2 = u)).card = Fintype.card G := by sorry
