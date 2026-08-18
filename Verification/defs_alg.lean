--Imports
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Notation.Defs
import Verification.defs_timeHT
--import Verification.proofs_timeHT

namespace Alg
open HofT

universe T

def fobsspace {κ : Type T} {n : ℕ} (τ : timeline κ (n + 1))
    (ρ : timeline κ n) : (Set (timeline κ n × timeline κ n)) :=
  {p | valid_timeline τ ∧ p.1 ∈ ffld τ ∧ p.2 = ρ}

def simobservable {κ : Type T} {n : ℕ} (A X : timeline κ n)
    (τ ρ γ : Set (timeline κ n × timeline κ n))
    (subvt : γ ⊆ ρ ∧ (∃ S, succs S γ = ffld γ)) :
    (m : ℕ) -> Prop
  | 0 => A ∈ ffld τ ∧ X ∈ ffld γ ∧ succs A τ = ffld τ \ {A} ∧ succs X γ = ffld γ \ {X}
  | m + 1 => ∃ B Y, is_imm_succ A B τ ∧ is_imm_succ Y X γ ∧ simobservable B Y τ ρ γ subvt m

def pimobservable {κ : Type T} {n : ℕ} (A X : timeline κ n)
    (τ ρ γ : Set (timeline κ n × timeline κ n))
    (subvt : γ ⊆ ρ ∧ (∃ S, succs S γ = ∅)) :
    (m : ℕ) -> Prop
  | 0 => A ∈ ffld τ ∧ X ∈ ffld γ ∧ succs A τ = ∅ ∧ succs X γ = ∅
  | m + 1 => ∃ B Y, is_imm_succ B A τ ∧ is_imm_succ Y X γ ∧ pimobservable B Y τ ρ γ subvt m

def imobsspace {κ : Type T} {n : ℕ} (τ ρ γ : Set (timeline κ n × timeline κ n))
    (subvt1 : γ ⊆ ρ ∧ (∃ S, succs S γ = ffld γ))
    (subvt2 : γ ⊆ ρ ∧ (∃ S, succs S γ = ffld γ)) :
    (Set (timeline κ n × timeline κ n)) :=
  {p | ∃ m ≥ 0, simobservable p.1 p.2 τ ρ γ subvt1 m ∨ simobservable p.1 p.2 τ ρ γ subvt2 m}

def obsspace {κ : Type T} {n : ℕ} (m : ℕ)
    (τ : Set (timeline κ (n + m) × timeline κ (n + m))) (ρ : timeline κ n) :
    (Set (timeline κ n × timeline κ n)) :=
  {S | S.1 ∈ fld n m τ ∧ S.2 = ρ}

def invobsspace {κ : Type T} {n : ℕ} (m : ℕ)
    (τ : Set (timeline κ (n + m) × timeline κ (n + m))) (ρ : timeline κ n) :
    (Set (timeline κ n × timeline κ n)) :=
  {S | S.2 ∈ fld n m τ ∧ S.1 = ρ}

def invimobsspace {κ : Type T} {n : ℕ} (τ ρ γ : Set (timeline κ n × timeline κ n))
    (subvt1 : γ ⊆ ρ ∧ (∃ S, succs S γ = ffld γ))
    (subvt2 : γ ⊆ ρ ∧ (∃ S, succs S γ = ffld γ)) :
    (Set (timeline κ n × timeline κ n)) :=
  {p | ∃ m ≥ 0, simobservable p.2 p.1 τ ρ γ subvt1 m ∨ simobservable p.2 p.1 τ ρ γ subvt2 m}

--def see {κ : Type T} {n : ℕ} (A B : timeline κ n) : (timeline)

--def bracket {κ : Type T} {n : ℕ} : (timeline κ n × timeline κ n)

--def add








end Alg
