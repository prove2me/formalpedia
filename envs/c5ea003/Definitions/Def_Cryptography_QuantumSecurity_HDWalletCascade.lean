-- Prove2me | Definitions.Def_Cryptography_QuantumSecurity_HDWalletCascade
-- name    : Cryptography_QuantumSecurity_HDWalletCascade
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:44:26.715314+00:00
-- url     : https://prove2.me/theorems/ca847c4b-6d49-4c32-a836-5b74d2fb6d46
-- title:
--   Aether Catalog definitions — Cryptography_QuantumSecurity_HDWalletCascade
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.QuantumSecurity.HDWalletCascade`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/QuantumSecurity/HDWalletCascade.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Cryptography.QuantumSecurity.HDWalletCascade

Auto-generated from theorem catalog database.
Domain: Cryptography/QuantumSecurity
Declarations: 19
-/

variable {n : ℕ}

/-- BIP-32 non-hardened child key derivation in ZMod n. -/
def bip32_child_key (parent_key offset : ZMod n) : ZMod n :=
  parent_key + offset



/-- Multi-level derivation: grandchild from parent through child. -/
def bip32_grandchild_key (parent_key offset₁ offset₂ : ZMod n) : ZMod n :=
  bip32_child_key (bip32_child_key parent_key offset₁) offset₂




/-- Number of non-hardened child keys per parent in BIP-32. -/
def bip32_children_per_level : ℕ := 2^31

/-- BIP-44 non-hardened keys: change (2) × address_index (2^31). -/
def bip44_nonhardened_keys : ℕ := 2 * 2^31






/-- Key derivation type -/
inductive DerivationType where
  | hardened
  | nonHardened
  deriving DecidableEq, Repr


