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

/-(X, 0, Y), and we have three projections, proj1 : (X, Y, 0) → (X, Y)
(X, 0, Y) → (X, Y), and (0, X, Y) → (X, Y).
We will only handle finite extensions for  the first paper.
Maybe later we can handle infinite extensions, but that would require substantive
revision of HT in order to get it all working.-/

/-def ext_pair {κ : Type T} {n : ℕ} (τ : (timeline κ n × timeline κ n)) :
    (timeline κ n × timeline κ n × timeline κ n)
  :=
-/
/-
def ext_timeline {κ : Type T} {n : ℕ} (τ : Set (timeline κ n × timeline κ n)) :
    Set (timeline κ n × timeline κ n × timeline κ n)
  := {p | p.2.2 = ∅ ∧ ∃ q ∈ τ, p.1 = q.1 ∧ p.2.1 = q.2}
-/
end Basis
