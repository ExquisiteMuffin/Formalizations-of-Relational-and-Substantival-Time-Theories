--Imports
import Mathlib.Logic.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Notation.Defs
import Verification.defs_timeHT

--Basis, used in proofs_timeB.lean only
namespace Basis

open HofT

universe T

def empt {κ : Type T} {n : ℕ} : timeline κ n := ∅

def ext_pair {κ : Type T} {n : ℕ} (τ : (timeline κ n × timeline κ n)) :
    (timeline κ n × timeline κ n × timeline κ n)
  :=

def ext_timeline {κ : Type T} {n : ℕ} (τ : Set (timeline κ n × timeline κ n)) :
    Set (timeline κ n × timeline κ n × timeline κ n)
  := {p | p.3 = empt ∧ ∃ q ∈ τ, p.1 = q.1 ∧ p.2 = q.2}

end Basis
