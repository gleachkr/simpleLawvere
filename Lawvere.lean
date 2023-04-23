import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Closed.Monoidal

open CategoryTheory

noncomputable instance cartesian [Category α] [Limits.HasFiniteProducts α] : MonoidalCategory α where
  tensorObj x y := Limits.prod x y
  tensorUnit' := Limits.terminal α
  tensorHom := by
    intros X Y Z W f g
    simp
    exact Limits.prod.lift (Limits.prod.fst ≫ f) (Limits.prod.snd ≫ g)
  rightUnitor X := Limits.prod.rightUnitor X
  leftUnitor X := Limits.prod.leftUnitor X
  associator X Y Z := Limits.prod.associator X Y Z

structure interpreter [Category α] [Limits.HasFiniteProducts α] [mc : MonoidalClosed α] 
  (A E Y : α) (i : E ⟶ Y)  where
  map : A ⟶ (A ⟶[α] E)
  interprets : ∀f : A ⟶ E, ∃c : cartesian.tensorUnit' ⟶ A, 
    let lhs := (Limits.prod.rightUnitor A).inv ≫ (Limits.prod.map (𝟙 A) (c ≫  map)) ≫ (ihom.ev A).app E ≫ i
    let rhs := f ≫ i
    lhs = rhs

def fixedPointProperty [Category α] [Limits.HasFiniteProducts α] { E Y : α } (i : E ⟶ Y) :=
  ∀t : E ⟶ E, ∃c: cartesian.tensorUnit' ⟶ E, c ≫  t ≫ i = c ≫  i

theorem lawvereGeneralized [Category α] [Limits.HasFiniteProducts α] [MonoidalClosed α] {A E Y : α} {i : E ⟶ Y}
  : Nonempty (interpreter A E Y i) → fixedPointProperty i := by
    intros 
    have ⟨int⟩ := ‹Nonempty (interpreter A E Y i)›
    clear ‹Nonempty (interpreter A E Y i)›
    let g := (Limits.prod.map (𝟙 A) int.map) ≫ (ihom.ev A).app E
    simp at g
    have fact : ∀f : A ⟶ E, ∃c : cartesian.tensorUnit' ⟶ A, ∀a : cartesian.tensorUnit' ⟶ A, 
      (Limits.prod.lift a c) ≫ g ≫ i = a ≫ f ≫ i := by
        intros f
        have ⟨f',eq₀⟩ := int.interprets f
        refine ⟨f',?_⟩
        intros a
        have termEq₁ : a ≫ Limits.terminal.from A = 𝟙 cartesian.tensorUnit' := by simp
        simp [←eq₀, Limits.prod.comp_lift_assoc]
        have termEq₂ : a ≫ Limits.terminal.from A ≫ f' ≫ int.map = (a ≫ Limits.terminal.from A) ≫ f' ≫ int.map := by rw [Category.assoc]
        rw [termEq₂,termEq₁]
        simp
    intros t
    let k : A ⟶ E := Limits.diag A ≫ g ≫ t
    have ⟨k',eq₁⟩ := fact k
    have eq₂ := eq₁ k'
    simp at eq₂
    have rweq : Limits.prod.lift k' (k' ≫ int.map) = k' ≫ Limits.prod.lift (𝟙 A) int.map := by simp
    refine ⟨Limits.prod.lift k' (k' ≫ int.map) ≫  (ihom.ev A).app E, ?_⟩
    simp
    rw [eq₂, rweq, Category.assoc]
