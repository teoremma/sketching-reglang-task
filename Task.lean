
import Lean
import Sketching.Sketch

set_option sketchRecord true

namespace RegExp
open Lean Elab

inductive Char where
  | z
  | o
deriving Repr

notation "c(0)" => Char.z
notation "c(1)" => Char.o

abbrev String := List Char


inductive RegExp : Type where
  | emp : RegExp
  | eps : RegExp
  | char : Char → RegExp
  | star : RegExp → RegExp
  | union : RegExp → RegExp → RegExp
  | concat : RegExp → RegExp → RegExp
deriving Nonempty, Inhabited, Repr


instance : Coe Char RegExp where
  coe c := RegExp.char c

notation "∅" => RegExp.emp
notation "ε" => RegExp.eps
notation r1 " <|> " r2  => RegExp.union r1 r2
notation r1 " <·> " r2 => RegExp.concat r1 r2
notation r "*" => RegExp.star r


inductive accepts : RegExp → String → Prop where
  | eps : accepts ε []
  | char (c : Char) : accepts c [c]
  | unionLeft r1 r2 s : accepts r1 s → accepts (r1 <|> r2) s
  | unionRight r1 r2 s : accepts r2 s → accepts (r1 <|> r2) s
  | concat r1 r2 s1 s2:
    accepts r1 s1 →
    accepts r2 s2 →
    accepts (r1 <·> r2) (s1 ++ s2)
  | starEmpty r : accepts (r*) []
  | starNonempty r s1 s2 :
    accepts r s1 →
    accepts (r*) s2 →
    accepts (r*) (s1 ++ s2)


def exp_all := (c(0) <|> c(1))*

def Language := String → Prop

def empty : Language := λ s => False
def all : Language := λ s => True

def is_regular (l : Language) := ∃ r, ∀ s, l s ↔ accepts r s

def union_lang (l₁ l₂ : Language) := λ s => l₁ s ∨ l₂ s

def concat_lang (l₁ l₂ : Language) := λ s => ∃ s₁ s₂, s = s₁ ++ s₂ ∧ l₁ s₁ ∧ l₂ s₂

def reverse_lang (l : Language) := λ (s : String) => ∃ s', s.reverse = s' ∧ l s'


-- PART 1 : Examples of Regular Expressions
theorem ex1 : accepts (c(0) <|> c(1)) [c(1)] := by
  apply accepts.unionRight
  apply accepts.char

theorem ex2 : accepts (c(0) <·> c(1)) ([c(0)] ++ [c(1)]) := by
  apply accepts.concat
  · apply accepts.char
  · apply accepts.char

theorem ex3 : accepts (c(1)*) [] := by
  apply accepts.starEmpty

theorem ex4 : accepts (c(1)*) ([c(1)] ++ ([c(1)] ++ [])) := by
  apply accepts.starNonempty
  · apply accepts.char
  apply accepts.starNonempty
  · apply accepts.char
  apply accepts.starEmpty


-- PART 2 : Warm up of `accepts`
theorem cons_app : forall (a : α) (l : List α), a :: l = [a] ++ l := by
  intros a l
  rfl

theorem accepts_concat : ∀ r₁ r₂ s₁ s₂, accepts r₁ s₁ → accepts r₂ s₂ → accepts (r₁ <·> r₂) (s₁ ++ s₂) := by
  sorry

theorem accepts_unionLeft : ∀ r₁ r₂ s, accepts r₁ s → accepts (r₁ <|> r₂) s := by
  sorry

theorem accepts_star_empty : ∀ r, accepts (r*) [] := by
  sorry

theorem accepts_char : ∀ (c : Char) s, accepts c s → s = [c] := by
  sorry

theorem rejects_emp : ∀ s, ¬ accepts ∅ s := by
  intros s h
  cases h

theorem accepts_not_emp : ∀ r, (∃ s, accepts r s) → r ≠ ∅ := by
  sorry

theorem empty_regular : is_regular empty := by
  exists ∅
  intro s
  constructor
  · intro h
    contradiction
  · intro h
    exact False.elim (rejects_emp s h)

theorem star_r : ∀ r s, accepts r s → accepts (r*) s := by
  intro r s
  intro h
  have : s = s ++ [] := by simp
  rw [this]
  apply accepts.starNonempty
  · exact h
  · exact accepts.starEmpty _

theorem union_comm : ∀ r₁ r₂ s, accepts (r₁ <|> r₂) s ↔ accepts (r₂ <|> r₁) s := by
  intros r₁ r₂ s
  constructor
  · intro h
    cases h
    · apply accepts.unionRight
      assumption
    · apply accepts.unionLeft
      assumption
  · intro h
    cases h
    · apply accepts.unionRight
      assumption
    · apply accepts.unionLeft
      assumption


-- PART 3 : Regular Languages (through regular expressions)
theorem accepts_exp_all : ∀ s, accepts exp_all s := by

  intros s
  induction s with
  | nil => apply accepts.starEmpty
  | cons hd tl ih =>
                     rw [cons_app hd tl]
                     apply accepts.starNonempty
                     ·
                       cases hd with
                       | z =>
                              apply accepts.unionLeft
                              apply accepts.char
                       | o =>
                              apply accepts.unionRight
                              apply accepts.char
                     · exact ih

theorem all_regular : is_regular all := by
  exists exp_all
  intro s
  constructor
  · intro _
    apply accepts_exp_all
  · intro _
    trivial

theorem union_regular : ∀ (l₁ l₂ : Language),
  is_regular l₁ →
  is_regular l₂ →
  is_regular (union_lang l₁ l₂) := by

  intros l₁ l₂ h₁ h₂
  cases h₁ with
  | intro r₁ hr₁ =>
    cases h₂ with
    | intro r₂ hr₂ =>
      exists (r₁ <|> r₂)
      intro s
      dsimp [union_lang]
      constructor
      · intro h
        cases h
        · apply accepts.unionLeft
          rw [← hr₁]
          assumption
        · apply accepts.unionRight
          rw [← hr₂]
          assumption
      · intro h
        cases h
        · left
          rw [hr₁]
          assumption
        · right
          rw [hr₂]
          assumption

theorem concat_regular : ∀ (l₁ l₂ : Language),
  is_regular l₁ →
  is_regular l₂ →
  is_regular (concat_lang l₁ l₂) := by

  intros l₁ l₂ h₁ h₂
  cases h₁ with
  | intro r₁ hr₁ =>
    cases h₂ with
    | intro r₂ hr₂ =>
      exists (r₁ <·> r₂)
      intro s
      dsimp [concat_lang]
      constructor
      · rintro ⟨s₁, s₂, h_eq, hl₁, hl₂⟩
        rw [hr₁] at hl₁
        rw [hr₂] at hl₂
        rw [h_eq]
        exact accepts.concat r₁ r₂ s₁ s₂ hl₁ hl₂
      · intro h
        cases h with
        | concat _ _ s₁ s₂ h₁' h₂' =>
          rw [← hr₁] at h₁'
          rw [← hr₂] at h₂'
          exact ⟨s₁, s₂, rfl, h₁', h₂'⟩


-- PART 4 : Regularity of Reversal
def reverse : RegExp → RegExp
  | .emp => ∅
  | .eps => ε
  | .char c => c
  | .star r => (reverse r)*
  | .union r₁ r₂ => (reverse r₁) <|> (reverse r₂)
  | .concat r₁ r₂ => (reverse r₂) <·> (reverse r₁)

def reverse_inv : ∀ r, reverse (reverse r) = r := by
  intro r
  induction r with
  | emp => rfl
  | eps => rfl
  | char c => rfl
  | star r ih => simp [reverse, ih]
  | union r₁ r₂ ih₁ ih₂ => simp [reverse, ih₁, ih₂]
  | concat r₁ r₂ ih₁ ih₂ => simp [reverse, ih₁, ih₂]

-- PART 4 a : Inversion lemmas for reverse
theorem reverse_invert_emp : ∀ r, reverse r = ∅ → r = ∅ := by
  intro r h
  cases r with
  | emp => rfl
  | eps => contradiction
  | char _ => contradiction
  | star _ => contradiction
  | union _ _ => contradiction
  | concat _ _ => contradiction

theorem reverse_invert_eps : ∀ r, reverse r = ε → r = ε := by
  sorry

theorem reverse_invert_char : ∀ r (c : Char), reverse r = c → r = c := by
  sorry

theorem reverse_invert_union : ∀ (r r₁ r₂ : RegExp),
  (reverse r = r₁ <|> r₂) → r = (reverse r₁) <|> (reverse r₂) := by
  sorry

theorem reverse_invert_cat : ∀ (r r₁ r₂ : RegExp),
  (reverse r = r₁ <·> r₂) → r = (reverse r₂) <·> (reverse r₁) := by
  sorry

theorem reverse_invert_star : ∀ r r', reverse r = r'* → r = (reverse r')* := by
  sorry


-- PART 4 b : Proving reversal correct
theorem lazy_star : ∀ r s₁ s₂, accepts (r*) s₁ → accepts r s₂ → accepts (r*) (s₁ ++ s₂) := by
  intros r s₁ s₂ h₁ h₂
  cases h₁ with
  | starEmpty => apply accepts.starNonempty; sorry; sorry
  | starNonempty r s₁' s₂' h₁' h₁'' =>
    apply accepts.starNonempty; sorry
    sorry;

theorem reverse_correct_mp : ∀ r s, accepts r s → accepts (reverse r) (s.reverse) := by
  sorry

theorem reverse_correct_mpr : ∀ r r' s s',
  reverse r = r' →
  s.reverse = s' →
  accepts r' s' → accepts r s := by
  sorry

theorem reverse_correct : ∀ r s, accepts r s ↔ accepts (reverse r) (s.reverse) := by
  sorry


-- PART 4 c : Proving reverse is regular
theorem reverse_regular : ∀ l, is_regular l → is_regular (reverse_lang l) := by
  sorry

end RegExp
