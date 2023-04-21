import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Closed.Monoidal

noncomputable instance cartesian [CategoryTheory.Category α] [CategoryTheory.Limits.HasFiniteProducts α] : CategoryTheory.MonoidalCategory α where
  tensorObj x y := CategoryTheory.Limits.prod x y
  tensorUnit' := CategoryTheory.Limits.terminal α
  tensorHom := by
    intros X Y Z W f g
    simp
    exact CategoryTheory.Limits.prod.lift (CategoryTheory.Limits.prod.fst ≫ f) (CategoryTheory.Limits.prod.snd ≫ g)
  rightUnitor X := CategoryTheory.Limits.prod.rightUnitor X
  leftUnitor X := CategoryTheory.Limits.prod.leftUnitor X
  associator X Y Z := CategoryTheory.Limits.prod.associator X Y Z

structure interpreter [CategoryTheory.Category α] [CategoryTheory.Limits.HasFiniteProducts α] [mc : CategoryTheory.MonoidalClosed α] 
  (A E Y : α) (i : E ⟶ Y)  where
  map : A ⟶ (A ⟶[α] E)
  interprets : ∀f : A ⟶ E, ∃c : cartesian.tensorUnit' ⟶ A, 
    let lhs := (cartesian.rightUnitor A).inv ≫ CategoryTheory.MonoidalClosed.uncurry (c ≫  map) ≫ i
    let rhs := f ≫ i
    lhs = rhs

def fixedPointProperty [CategoryTheory.Category α] [CategoryTheory.Limits.HasFiniteProducts α] { E Y : α } (i : E ⟶ Y) :=
  ∀t : E ⟶ E, ∃c: cartesian.tensorUnit' ⟶ E, c ≫  t ≫ i = c ≫  i

theorem lawvereGeneralized [CategoryTheory.Category α] [CategoryTheory.Limits.HasFiniteProducts α] [CategoryTheory.MonoidalClosed α] {A E Y : α} {i : E ⟶ Y}
  : Nonempty (interpreter A E Y i) → fixedPointProperty i := by
    intros 
    have ⟨int⟩ := ‹Nonempty (interpreter A E Y i)›
    clear ‹Nonempty (interpreter A E Y i)›
    let g := (CategoryTheory.Limits.prod.map (𝟙 A) int.map) ≫ (CategoryTheory.ihom.ev A).app E
    simp at g
    sorry

