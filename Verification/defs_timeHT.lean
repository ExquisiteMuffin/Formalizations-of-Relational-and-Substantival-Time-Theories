--Imports - Change later to fit only the definitions used
import Mathlib

namespace HofT

universe T

--A, B, C, D

-- {(A. B), (B, C), (C, D)}

--Moment defined via timeline α 0.
def timeline (α : Type T) : ℕ → Type T
  | 0 => α
  | n + 1 => Set (timeline α n × timeline α n)

--Determines if it is a set with single
def single {n : ℕ} {κ : Type T} (τ : Set (timeline κ n × timeline κ n)) : Prop
  := τ.Nonempty ∧ (∃ q, ∀ p, p ∈ τ ↔ p = q)

--Order pairs defined, vacuously true here if n ≤ 0, hp. must include n > 0.
def ordered {n : ℕ} {κ : Type T} (τ : Set (timeline κ n × timeline κ n)) : Prop
  := single τ ∨ (τ.Nonempty → ∀ p ∈ τ, ∃ q ∈ τ, p ≠ q ∧ (p.1 = q.2 ∨ p.2 = q.1))

def nonbranching {n : ℕ} {κ : Type T} (τ : Set (timeline κ n × timeline κ n)) : Prop
  := ∀ p ∈ τ, ∀ q ∈ τ, p.1 = q.1 ↔ p.2 = q.2

def strictly_ordered {n : ℕ} {κ : Type T} (τ : Set (timeline κ n × timeline κ n))
  := ∀ A, ∀ B, ∀ p ∈ τ, ∀ q ∈ τ, (p.1 = A ∧ p.2 = B) → (q.2 ≠ A ∨ q.1 ≠ B)

def valid_timeline {n : ℕ} {κ : Type T} (τ : Set (timeline κ n × timeline κ n)) : Prop
  := nonbranching τ ∧ ordered τ ∧ strictly_ordered τ ∧ τ.Nonempty

--Defines
def order_set {κ : Type T} (n : ℕ) : Set (Set (timeline κ n × timeline κ n))
  := {τ | valid_timeline τ}

def fdom {n : ℕ} {κ : Type T} (τ : Set (timeline κ n × timeline κ n)) : Set (timeline κ n)
  := {x : timeline κ n | τ ∈ (order_set n) ∧ (∃ p ∈ τ, p.1 = x)}

def fran {n : ℕ} {κ : Type T} (τ : Set (timeline κ n × timeline κ n)) : Set (timeline κ (n))
  := {y : timeline κ n | τ ∈ (order_set n) ∧ (∃ p ∈ τ, p.2 = y)}

def ffld {n : ℕ} {κ : Type T} (τ : Set (timeline κ n × timeline κ n)) : Set (timeline κ (n))
  := {s : timeline κ n | τ ∈ (order_set n) ∧ (∃ p ∈ τ, p.1 = s ∨ p.2 = s)}

--The commented out defintion beneath is going to be proved equivalent
--in a theorem in proofs_timeHT.lean
def fld {κ : Type T} (n : ℕ) :
    (m : ℕ) → Set (timeline κ (n + m) × timeline κ (n + m)) → Set (timeline κ n)
  | 0, τ => {s | valid_timeline τ ∧ (∃ p ∈ τ, p.1 = s ∨ p.2 = s)}
  | m + 1, τ => {s | valid_timeline τ ∧ ∃ y ∈ τ, s ∈ fld n m y.1 ∨ s ∈ fld n m y.2}

/-def fld {κ : Type T} (n : ℕ) : (m : ℕ) → Set (timeline κ (n + m)) → Set (timeline κ n)
  | 0, S => S
  | m + 1, S => {A | ∃ p ∈ fld n m S, ∃ B ∈ order (n), {(A, B)} ⊆ p ∨ {(B, A) ⊆ p}}
-/

def subt {n : ℕ} {κ : Type T} (τ : Set (timeline κ n × timeline κ n))
    (ρ : Set (timeline κ n × timeline κ n)) :
    Set (timeline κ n × timeline κ n)
  := {S | S ∈ τ ∧ ¬(S ∈ ρ)}

def is_imm_succ {n : ℕ} {κ : Type T} (B A : timeline κ n)
    (τ : Set (timeline κ n × timeline κ n)) :
    Prop
  := valid_timeline τ ∧ ∃ X ∈ τ, X.1 = A ∧ X.2 = B

def imm_succs {n : ℕ} {κ : Type T} (A : timeline κ n) (τ : Set (timeline κ n × timeline κ n)) :
    Set (timeline κ n)
  := {B | is_imm_succ B A τ}

--To prove:
/-
def imm_succs {n : ℕ} {κ : Type T} (A : timeline κ n) (τ : Set (timeline κ n × timeline κ n)) :
    Set (timeline κ n)
  := {B | ∃ p ∈ τ, p.1 = A ∧ p.2 = B}
-/

--Defines the (C, D) for which C = B and succeeds (A, B) in some timeline τ.
def imm_links {n : ℕ} {κ : Type T} (A B : timeline κ n) (τ : Set (timeline κ n × timeline κ n)) :
    Set (timeline κ n × timeline κ n)
  := {ℓ | B ∈ imm_succs A τ ∧ ℓ.1 = B ∧ ∃ p ∈ τ, p.2 = ℓ.2 ∧ p.1 = ℓ.1}

--Probabyl not useful
def indr_succ {n : ℕ} {κ : Type T} (B A : timeline κ n) (τ : Set (timeline κ n × timeline κ n)) :
    Prop
  := ∃ x ∈ τ, valid_timeline τ ∧ (A, x.2) ∈ τ ∧ (x.2, B) ∈ τ

def is_succ {n : ℕ} {κ : Type T} (B A : timeline κ n) (τ : Set (timeline κ n × timeline κ n)) :
    (m : ℕ) → Prop
  | 0 => False
  | 1 => is_imm_succ B A τ
  | m + 1 => m > 0 ∧ ∃ X, (is_succ X A τ m ∧ is_imm_succ B X τ)

def succs {n : ℕ} {κ : Type T} (A : timeline κ n) (τ : Set (timeline κ n × timeline κ n)) :
    Set (timeline κ n)
  := {s | ∃ m > 0, is_succ s A τ m}

def preds {n : ℕ} {κ : Type T} (A : timeline κ n) (τ : Set (timeline κ n × timeline κ n)) :
    Set (timeline κ n)
  := {s | s ∈ ffld τ ∧ A ∈ ffld τ ∧ ¬(s ∈ succs A τ) ∧ s ≠ A}

def inv_timeline {n : ℕ} {κ : Type T} (τ : Set (timeline κ n × timeline κ n)) :
    Set (timeline κ n × timeline κ n)
  := {p | ∃ q ∈ τ, p.1 = q.2 ∧ p.2 = q.1}

def inv_pair {n : ℕ} {κ : Type T} (p : timeline κ n × timeline κ n) :
    timeline κ n × timeline κ n
  := (p.2, p.1)

def tdisp {n : ℕ} {κ : Type T} (B A : timeline κ n)
    (τ : Set (timeline κ n × timeline κ n)) :
    Set (timeline κ n × timeline κ n)
  := by classical exact
    if (B ∈ succs A τ)
      then ((subt τ {s | s ∈ τ ∧ s.2 ∈ (succs B τ)}) ∩ (subt τ {s | s ∈ τ ∧ s.1 ∈ (preds A τ)}))
    else if (A ∈ succs B τ)
      then ((subt τ {s | s ∈ τ ∧ s.2 ∈ (succs A τ)}) ∩ (subt τ {s | s ∈ τ ∧ s.1 ∈ (preds B τ)}))
    else
      ∅

/-
In the fld call, k represents the order of the timeline you wish your set members to be
while m represents the beginning order of the timeline minus one. Thus, the order of a timeline
n is given by m + 1 = n.
-/
noncomputable def tdist {κ : Type T} (k : ℕ) :
    (m : ℕ)
    → (B A : timeline κ (k + m))
    → (τ : Set (timeline κ (k + m) × timeline κ (k + m)))
    → ℕ∞
  | m, B, A, τ => Set.encard (fld k m (tdisp B A τ)) - 1


end HofT
