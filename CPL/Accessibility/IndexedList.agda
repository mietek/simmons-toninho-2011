open import Prelude
open import CPL.Accessibility.Inductive

module CPL.Accessibility.IndexedList (UWF : UpwardsWellFounded) where

  open SuccStar UWF

  data Item (A : Set) : Set where
    _at_ : A → W → Item A

  IList : Set → Set
  IList A = ListT (Item A)

  -- Equivalence at a given world
  infix 0 _⊆_at_
  _⊆_at_ : ∀{A} → IList A → IList A → W → Set 
  Δ ⊆ Γ at w = ∀{A w'} → A at w' ∈ Δ → (A at w' ∈ Γ) + (w ⊀ w')

  -- Elimination forms
  ⊆at/now : ∀{A w Δ Γ}{x : A} 
       → Δ ⊆ Γ at w
       → (x at w) ∈ Δ 
       → (x at w) ∈ Γ
  ⊆at/now sub iN with sub iN
  ... | Inl iN' = iN'
  ... | Inr ¬ω = abort (¬ω ≺*≡)

  ⊆at/later : ∀{A w w' Δ Γ}{x : A} 
       → w ≺+ w' 
       → Δ ⊆ Γ at w 
       → (x at w') ∈ Δ 
       → (x at w') ∈ Γ
  ⊆at/later ω sub iN with sub iN
  ... | Inl iN' = iN'
  ... | Inr ¬ω = abort (¬ω (≺*+ ω))

  -- Introduction forms
  ⊆at/≺ : ∀{A w w'}{Δ Γ : IList A} 
       → w ≺ w' 
       → Δ ⊆ Γ at w 
       → Δ ⊆ Γ at w'
  ⊆at/≺ ω sub iN with sub iN
  ... | Inl iN' = Inl iN'
  ... | Inr ¬ω = Inr (⊀trans ω ¬ω)

  ⊆at/≺+ : ∀{A w w'}{Δ Γ : IList A} 
       → w ≺+ w' 
       → Δ ⊆ Γ at w 
       → Δ ⊆ Γ at w'
  ⊆at/≺+ (≺+0 ω) sub = ⊆at/≺ ω sub
  ⊆at/≺+ (≺+S ω ω+) sub = ⊆at/≺+ ω+ (⊆at/≺ ω sub)

  ⊆at/refl : ∀{w A}(Δ : IList A)
       → Δ ⊆ Δ at w
  ⊆at/refl Δ iN = Inl iN

  ⊆at/wken : ∀{A Γ Δ w w'}{x : A} 
       → Δ ⊆ Γ at w 
       → Δ ⊆ ((x at w') :: Γ) at w
  ⊆at/wken sub iN with sub iN
  ... | Inl iN' = Inl (S iN')
  ... | Inr ω = Inr ω

  ⊆at/irrev : ∀{A Γ Δ w w'}{x : A} 
       → w ⊀ w' 
       → Δ ⊆ Γ at w 
       → ((x at w') :: Δ) ⊆ Γ at w
  ⊆at/irrev ω sub Z = Inr ω
  ⊆at/irrev ω sub (S iN) = sub iN

  ⊆at/both : ∀{A Γ Δ w w'}{x : A}
       → Δ ⊆ Γ at w 
       → ((x at w') :: Δ) ⊆ ((x at w') :: Γ) at w
  ⊆at/both sub Z = Inl Z
  ⊆at/both sub (S iN) with sub iN
  ... | Inl iN' = Inl (S iN')
  ... | Inr n≺ = Inr n≺

  -- Equivalence of contexts up to a given world, equality beyond that point
  data _⊆_to_ {A : Set} : IList A → IList A → W → Set where
    st : ∀{Δ Γ w}
         → Δ ⊆ Γ at w
         → (∀{w'} → w ≺+ w' → Γ ⊆ Δ at w')
         → Δ ⊆ Γ to w

  -- Elimination forms
  ⊆to/now : ∀{A w Δ Γ}{x : A} 
       → Δ ⊆ Γ to w 
       → (x at w) ∈ Δ 
       → (x at w) ∈ Γ
  ⊆to/now (st sub sub≺) iN = ⊆at/now sub iN

  ⊆to/later : ∀{A w w' Δ Γ}{x : A} 
       → w ≺+ w' 
       → Δ ⊆ Γ to w 
       → (x at w') ∈ Δ 
       → (x at w') ∈ Γ
  ⊆to/later ω (st sub sub≺) iN = ⊆at/later ω sub iN

  ⊆to/later' : ∀{A w w' Δ Γ}{x : A} 
       → w ≺+ w' 
       → Δ ⊆ Γ to w 
       → (x at w') ∈ Γ 
       → (x at w') ∈ Δ
  ⊆to/later' ω (st sub sub≺) iN with sub≺ ω iN
  ... | Inl iN' = iN'
  ... | Inr ¬ω = abort (¬ω ≺*≡)

  -- Introduction forms
  ⊆to/≺ : ∀{A w w'}{Δ Γ : IList A} → w ≺+ w' → Δ ⊆ Γ to w → Δ ⊆ Γ to w'
  ⊆to/≺ ω (st sub sub≺) = st (⊆at/≺+ ω sub) (λ ω' → sub≺ (≺+trans ω ω')) 

  ⊆to/≺' : ∀{A w w'}{Δ Γ : IList A} → w ≺+ w' → Δ ⊆ Γ to w → Γ ⊆ Δ to w'
  ⊆to/≺' ω (st sub sub≺) = st (sub≺ ω) (λ ω' → ⊆at/≺+ (≺+trans ω ω') sub)

  ⊆to/refl : ∀{A w}(Δ : IList A) → Δ ⊆ Δ to w 
  ⊆to/refl Δ = st (⊆at/refl Δ) (λ ω → ⊆at/refl Δ)

  ⊆to/wken : ∀{A Γ Δ w}{x : A}
       → Δ ⊆ Γ to w 
       → Δ ⊆ ((x at w) :: Γ) to w
  ⊆to/wken (st sub sub≺) 
   = st (⊆at/wken sub) (λ ω' → ⊆at/irrev (≺+⊀ ω') (sub≺ ω'))

  ⊆to/irrev : ∀{A Γ Δ w w'}{x : A}
       → w ⊀ w'
       → Δ ⊆ Γ to w 
       → ((x at w') :: Δ) ⊆ Γ to w
  ⊆to/irrev ω (st sub sub≺) 
   = st (⊆at/irrev ω sub) (λ ω' → ⊆at/wken (sub≺ ω'))

  ⊆to/both : ∀{A Γ Δ w w'}{x : A}
       → Δ ⊆ Γ to w 
       → ((x at w') :: Δ) ⊆ ((x at w') :: Γ) to w
  ⊆to/both (st sub sub≺) = st (⊆at/both sub) (λ ω → ⊆at/both (sub≺ ω))

  -- Adding indices at a given world
  _atΓ_ : ∀{A} → ListT A → W → IList A
  Γ atΓ w = List.map (λ x → x at w) Γ

  ∈atΓ₁ : ∀{A Γ w}{x : A} → x ∈ Γ → (x at w) ∈ (Γ atΓ w)
  ∈atΓ₁ Z = Z
  ∈atΓ₁ (S iN) = S (∈atΓ₁ iN)

  ∈atΓ₂ : ∀{A Γ w}{x : A} → (x at w) ∈ (Γ atΓ w) → x ∈ Γ 
  ∈atΓ₂ {A} {[]} ()
  ∈atΓ₂ {A} {y :: y'} Z = Z
  ∈atΓ₂ {A} {y :: y'} (S iN) = S (∈atΓ₂ iN)

  -- Restriction
  _↓_ : ∀{A} → IList A → W → IList A
  [] ↓ w = []
  ((A at w') :: Γ) ↓ w with w ≡? w'
  ((A at .w) :: Γ) ↓ w | Inl Refl = Γ ↓ w
  ((A at w') :: Γ) ↓ w | Inr neq = (A at w') :: (Γ ↓ w)

  extend↓ : ∀{A w Γ}{x : A} → (((x at w) :: Γ) ↓ w) ≡ (Γ ↓ w)
  extend↓ {_}{w} with w ≡? w
  ... | Inl Refl = refl
  ... | Inr neq = abort (neq refl)

  ⊆at/↓ : ∀{A} → (Γ : IList A) {w : W} → (Γ ↓ w) ⊆ Γ at w
  ⊆at/↓ [] = λ()
  ⊆at/↓ ((x at wx) :: Γ) {w} with w ≡? wx
  ⊆at/↓ ((x at .w) :: Γ) {w} | Inl Refl = ⊆at/wken (⊆at/↓ Γ)
  ⊆at/↓ ((x at wx) :: Γ) {w} | Inr neq = ⊆at/both (⊆at/↓ Γ)

  ⊆at/↓≺ : ∀{A} → (Γ : IList A) {w w' : W} → w ≺+ w' → Γ ⊆ (Γ ↓ w) at w'
  ⊆at/↓≺ [] ω = λ()
  ⊆at/↓≺ ((x at wx) :: Γ) {w} ω with w ≡? wx
  ⊆at/↓≺ ((x at .w) :: Γ) {w} ω | Inl Refl = ⊆at/irrev (≺+⊀ ω) (⊆at/↓≺ Γ ω)
  ⊆at/↓≺ ((x at wx) :: Γ) {w} ω | Inr neq = ⊆at/both (⊆at/↓≺ Γ ω)

  ⊆to/↓ : ∀{A} → (Γ : IList A) {w : W} → (Γ ↓ w) ⊆ Γ to w
  ⊆to/↓ Γ = st (⊆at/↓ Γ) (λ ω → ⊆at/↓≺ Γ ω)

  ⊆to/↓≺ : ∀{A} → (Γ : IList A) {w w' : W} → w ≺+ w' → Γ ⊆ (Γ ↓ w) to w'
  ⊆to/↓≺ Γ ω = st (⊆at/↓≺ Γ ω) (λ ω' → ⊆at/≺+ (≺+trans ω ω') (⊆at/↓ Γ))

  -- Specific instances of generalized weakening
  exch/at : ∀{A Γ w'' w w'}{x y : A} 
       → ((x at w) :: (y at w') :: Γ) ⊆ ((y at w') :: (x at w) :: Γ) at w''
  exch/at Z = Inl (S Z) 
  exch/at (S Z) = Inl Z
  exch/at {_}{Γ}{w''} (S (S iN)) with ⊆at/refl {w''} Γ iN
  ... | Inl iN' = Inl (S (S iN'))
  ... | Inr ¬ω = Inr ¬ω 

  exch : ∀{A Γ w'' w w'}{x y : A}
       → ((x at w) :: (y at w') :: Γ) ⊆ ((y at w') :: (x at w) :: Γ) to w''
  exch = st exch/at (λ ω → exch/at)

  wken : ∀{A Γ w}{x : A} → Γ ⊆ ((x at w) :: Γ) to w
  wken = ⊆to/wken (⊆to/refl _)

  wkex : ∀{A Γ w w'}{x y : A} 
       → ((y at w') :: Γ) ⊆ ((y at w') :: (x at w) :: Γ) to w
  wkex = ⊆to/both (⊆to/wken (⊆to/refl _))