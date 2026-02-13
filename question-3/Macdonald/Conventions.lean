import Mathlib.Data.Real.Basic

namespace Macdonald
namespace Conventions

/-!
Phase 0: convention freeze for the long-form formalization effort.
-/

inductive QSpecialization where
  | general
  | qOne
deriving DecidableEq, Repr

inductive HeckeNormalization where
  | demazureLusztig
deriving DecidableEq, Repr

def chosenQSpecialization : QSpecialization := .qOne
def chosenHeckeNormalization : HeckeNormalization := .demazureLusztig

theorem chosen_q_is_qOne : chosenQSpecialization = .qOne := rfl
theorem chosen_hecke_normalization :
    chosenHeckeNormalization = .demazureLusztig := rfl

abbrev SpectralParameters (n : ℕ) (R : Type*) := Fin n → R
abbrev WordState (Species : Type*) (n : ℕ) := Fin n → Species
abbrev Composition (n : ℕ) := Fin n → ℕ

def wordCompositionEquiv (n : ℕ) : WordState ℕ n ≃ Composition n := Equiv.refl _

theorem wordCompositionEquiv_apply (n : ℕ) (w : WordState ℕ n) :
    wordCompositionEquiv n w = w := rfl

end Conventions
end Macdonald
