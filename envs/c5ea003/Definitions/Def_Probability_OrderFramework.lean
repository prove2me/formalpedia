-- Prove2me | Definitions.Def_Probability_OrderFramework
-- name    : Probability_OrderFramework
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:17.715634+00:00
-- url     : https://prove2.me/theorems/b5b92822-df93-4eb9-8f2a-9c377efc02e4
-- title:
--   Aether Catalog definitions — Probability_OrderFramework
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.OrderFramework`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/OrderFramework.lean by skeleton subtraction
import Mathlib
/-
  An Abstract Order Framework for Minor-Closed Classes
  ====================================================

  This file provides the abstract order-theoretic scaffolding used by
  `ForestDensity.lean` and `MinorModel.lean`: a *minor-closed class* is nothing
  but a downward-closed set in a preorder, and the classes obtained by
  *excluding* a family of graphs are exactly the basic examples.

  Main results:

  * `MinorTheory.MinorClosed`          : downward closure in a preorder.
  * `MinorTheory.excl_minorClosed`     : excluding any family gives a
                                         minor-closed class.
  * `MinorTheory.minorClosed_iff_isLowerSet` : the framework coincides with
                                         Mathlib's `IsLowerSet`.
  * closure of minor-closed classes under arbitrary unions and intersections.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): all the combinatorics of "minor-closed class" that
    is used downstream is order-theoretic, hence should be stated for an
    arbitrary preorder `α` and specialised later to `SimpleGraph V` with either
    the subgraph order or the genuine minor order.
  Experiment (Experimenter): defined `MinorClosed` as downward closure and
    verified that `excl S`, arbitrary unions, arbitrary intersections and
    complements-of-upper-sets all fit.
  Analysis (Analyst): `MinorClosed C ↔ IsLowerSet C` on the nose, so the whole
    Mathlib lower-set API becomes available to the graph-minor development.
  Critique (Critic): the framework is deliberately *order-theoretic only*; it
    says nothing about the graph-minor relation being a preorder — that is the
    content of `HadwigerCore.isMinor_trans`.
  Synthesis (PI): a small, reusable base layer.
  -- !-- Lab Notes -- !--
-/

namespace MinorTheory

variable {α : Type*} [Preorder α]

/-- A class of objects is **minor-closed** when it is downward closed for the
ambient order (which downstream is either the subgraph order or the graph-minor
order). -/
def MinorClosed (C : Set α) : Prop := ∀ ⦃G H : α⦄, G ≤ H → H ∈ C → G ∈ C

/-- The class of objects **excluding** every member of `S`. -/
def excl (S : Set α) : Set α := {G | ∀ H ∈ S, ¬ H ≤ G}











end MinorTheory


