-- Prove2me | Definitions.Def_Cryptography_GameTheory_MigrationGameTheory
-- name    : Cryptography_GameTheory_MigrationGameTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:13:38.378085+00:00
-- url     : https://prove2.me/theorems/7d2f5d9e-92ad-4b77-a165-50aa7a28ce93
-- title:
--   Aether Catalog definitions — Cryptography_GameTheory_MigrationGameTheory
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.GameTheory.MigrationGameTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/GameTheory/MigrationGameTheory.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Cryptography.QuantumSecurity.MigrationGameTheory

Auto-generated from theorem catalog database.
Domain: Cryptography/QuantumSecurity
Declarations: 43
-/

/-- Migration cost components (basis points of holdings). -/
structure MigrationCost where
  transaction_fee : ℕ
  size_overhead : ℕ
  complexity_risk : ℕ
  opportunity_cost : ℕ

/-- Estimated migration cost for a typical user. -/
def typical_migration_cost : MigrationCost := ⟨50, 1500, 10, 100⟩

/-- Total one-time migration cost (basis points). -/
def total_cost (c : MigrationCost) : ℕ :=
  c.transaction_fee + c.complexity_risk + c.opportunity_cost


/-- Expected loss from quantum attack. -/
def expected_quantum_loss (prob_bps holdings : ℕ) : ℕ :=
  prob_bps * holdings / 10000


/-- **Theorem**: Data on a public blockchain is always SNDL-exposed. -/
inductive StorableData where
  | publicKey | signedTransaction | encryptedComms
  deriving DecidableEq, Repr

/-- All blockchain data is already exposed. -/
def already_exposed : StorableData → Bool
  | _ => true


/-- New transactions per day across Bitcoin and Ethereum. -/
def new_bitcoin_txns_per_day : ℕ := 300000

/-- [Section: # CatalogBuild.Cryptography.QuantumSecurity.MigrationGameTheory
Auto-generated from theorem catalog database.
Domain: Cryptography/QuantumSecurity
Declarations: 43] -/
def new_ethereum_txns_per_day : ℕ := 1000000

/-- [Section: # CatalogBuild.Cryptography.QuantumSecurity.MigrationGameTheory
Auto-generated from theorem catalog database.
Domain: Cryptography/QuantumSecurity
Declarations: 43] -/
def daily_sndl_growth : ℕ := new_bitcoin_txns_per_day + new_ethereum_txns_per_day


/-- Payoff parameters -/
structure GameParams where
  migration_cost : ℤ
  quantum_loss : ℤ
  quantum_probability : ℕ  -- basis points (0-10000)
  network_effect : ℤ

/-- Default game parameters (10-year horizon). -/
def default_params : GameParams :=
  ⟨-160, -10000, 500, 50⟩

/-- Expected payoff for migrating. -/
def payoff_migrate (p : GameParams) : ℤ :=
  p.migration_cost + p.network_effect

/-- Expected payoff for staying (risk of quantum loss). -/
def payoff_stay (p : GameParams) : ℤ :=
  (p.quantum_probability : ℤ) * p.quantum_loss / 10000


/-- Prior probability of quantum ECDLP break within N years (basis points). -/
def prior_probability (years : ℕ) : ℕ :=
  if years < 10 then 100
  else if years < 15 then 500
  else if years < 20 then 2000
  else 5000

/-- Likelihood ratio from Willow-class advances. -/
def willow_likelihood_ratio : ℕ := 3

/-- Posterior probability after Bayesian update. -/
def posterior_probability (prior lr : ℕ) : ℕ :=
  min 10000 (prior * lr)




/-- Fork readiness stages -/
inductive ForkStage where
  | research | specification | implementation | testing | activation
  deriving DecidableEq, Repr

/-- Estimated time for each stage (months). -/
def stage_duration : ForkStage → ℕ
  | ForkStage.research       => 12
  | ForkStage.specification  => 6
  | ForkStage.implementation => 12
  | ForkStage.testing         => 12
  | ForkStage.activation      => 6




 -- 96 months = 8 years

/-- Bitcoin market cap (billions USD). -/
def btc_market_cap_billion : ℕ := 1700

def at_risk_pct : ℕ := 57


/-- Ethereum market cap (billions USD). -/
def eth_market_cap_billion : ℕ := 450

def eth_at_risk_pct : ℕ := 100


/-- DeFi TVL at risk. -/
def defi_tvl_billion : ℕ := 50


/-- Migration strategies ordered by aggressiveness. -/
inductive MigrationStrategy where
  | doNothing | monitorOnly | hybridAddresses
  | softForkPQOption | hardForkPQMandatory | emergencyFreeze
  deriving DecidableEq, Repr

/-- Expected value preservation (basis points). -/
def strategy_value_preserved : MigrationStrategy → ℕ
  | MigrationStrategy.doNothing            => 4300
  | MigrationStrategy.monitorOnly          => 4300
  | MigrationStrategy.hybridAddresses      => 7000
  | MigrationStrategy.softForkPQOption     => 8500
  | MigrationStrategy.hardForkPQMandatory  => 9500
  | MigrationStrategy.emergencyFreeze      => 10000


