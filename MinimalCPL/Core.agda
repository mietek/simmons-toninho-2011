-- A Constructive Logic of Provability
-- The minimal, propositional fragment
-- Robert J. Simmons, Bernardo Toninho

-- Necessary; no hope for Agda's positivity checker to work here
{-# OPTIONS --no-positivity-check #-}

module MinimalCPL.Core where
open import Prelude
open import Accessibility.Inductive
open import Accessibility.IndexedList

module CORE (UWF : UpwardsWellFounded) where 
   open UpwardsWellFounded UWF
   open ILIST UWF

   -- Types/Propositions
   infixr 10 _⊃_
   data Type : Set where
      a   : (N : Nat) → Type
      _⊃_ : (A B : Type) → Type
      □   : (A : Type) → Type
      ◇   : (A : Type) → Type
      ¬□  : (A : Type) → Type
      ¬◇  : (A : Type) → Type

   -- Contexts
   Ctx = List Type
   MCtx = IList Type

   infix 10 _,_[_]
   _,_[_] : MCtx → Type → W → MCtx
   Δ , A [ w ] = (A at w) :: Δ

   -- Natural deduction without a metric
   infix 1 _⊢_[_]
   data _⊢_[_] : MCtx → Type → W → Set where
      hyp : ∀{A Γ w}
         → (A at w ∈ Γ)
         → Γ ⊢ A [ w ]
      ⊃I : ∀{Γ A B w}
         → A at w :: Γ ⊢ B [ w ]
         → Γ ⊢ A ⊃ B [ w ]
      ⊃E : ∀{Γ A B w}
         → Γ ⊢ A ⊃ B [ w ]
         → Γ ⊢ A [ w ]
         → Γ ⊢ B [ w ]
      □I : ∀{Γ A w}
         → (∀{w'} → w ≺ w' → Γ ⊢ A [ w' ])
         → Γ ⊢ □ A [ w ]
      □E : ∀{Γ A C w}
         → Γ ⊢ □ A [ w ]
         → ((∀{w'} → w ≺ w' → Γ ⊢ A [ w' ]) → Γ ⊢ C [ w ])
         → Γ ⊢ C [ w ]
      ◇I : ∀{Γ A w w'}
         → w ≺ w'
         → Γ ⊢ A [ w' ]
         → Γ ⊢ ◇ A [ w ]
      ◇E : ∀{Γ A C w}
         → Γ ⊢ ◇ A [ w ] 
         → (∀{w'} → w ≺ w' → Γ ⊢ A [ w' ] → Γ ⊢ C [ w ])
         → Γ ⊢ C [ w ]
      ¬□I : ∀{Γ A w}
         → (∀{w'} → w ≺ w' → Γ ⊢ A [ w' ] → ⊥)
         → Γ ⊢ ¬□ A [ w ]
      ¬□E : ∀{Γ A C w}
         → Γ ⊢ ¬□ A [ w ]
         → ((∀{w'} → w ≺ w' → Γ ⊢ A [ w' ] → ⊥) → Γ ⊢ C [ w ])
         → Γ ⊢ C [ w ]
      ¬◇I : ∀{Γ A w w'}
         → w ≺ w'
         → (Γ ⊢ A [ w' ] → ⊥)
         → Γ ⊢ ¬◇ A [ w ]
      ¬◇E : ∀{Γ A C w}
         → Γ ⊢ ¬◇ A [ w ] 
         → (∀{w'} → w ≺ w' → (Γ ⊢ A [ w' ] → ⊥) → Γ ⊢ C [ w ])
         → Γ ⊢ C [ w ]

   -- Sequent calculus without a metric
   infix 1 _⇒_[_]
   data _⇒_[_] : MCtx → Type → W → Set where
      hyp : ∀{Q Γ w}
         → a Q at w ∈ Γ
         → Γ ⇒ a Q [ w ]
      ⊃R : ∀{Γ A B w}
         → (A at w) :: Γ ⇒ B [ w ]
         → Γ ⇒ A ⊃ B [ w ]
      ⊃L : ∀{Γ A B C w}
         → (A ⊃ B) at w ∈ Γ  
         → Γ ⇒ A [ w ]
         → (B at w) :: Γ ⇒ C [ w ]
         → Γ ⇒ C [ w ]
      □R : ∀{Γ A w}
         → (∀{w'} → w ≺ w' → Γ ⇒ A [ w' ]) 
         → Γ ⇒ □ A [ w ]
      □L : ∀{Γ A C w}
         → (□ A) at w ∈ Γ
         → ((∀{w'} → w ≺ w' → Γ ⇒ A [ w' ]) → Γ ⇒ C [ w ])
         → Γ ⇒ C [ w ]
      ◇R : ∀{Γ A w w'}
         → w ≺ w'
         → Γ ⇒ A [ w' ]
         → Γ ⇒ ◇ A [ w ]
      ◇L : ∀{Γ A C w}
         → (◇ A) at w ∈ Γ
         → (∀{w'} → w ≺ w' → Γ ⇒ A [ w' ] → Γ ⇒ C [ w ])
         → Γ ⇒ C [ w ]
      ¬□R : ∀{Γ A w}
         → (∀{w'} → w ≺ w' → Γ ⇒ A [ w' ] → ⊥)
         → Γ ⇒ ¬□ A [ w ]
      ¬□L : ∀{Γ A C w}
         → (¬□ A) at w ∈ Γ
         → ((∀{w'} → w ≺ w' → Γ ⇒ A [ w' ] → ⊥) → Γ ⇒ C [ w ])
         → Γ ⇒ C [ w ]
      ¬◇R : ∀{Γ A w w'}
         → w ≺ w'
         → (Γ ⇒ A [ w' ] → ⊥)
         → Γ ⇒ ¬◇ A [ w ] 
      ¬◇L : ∀{Γ A w C}
         → (¬◇ A) at w ∈ Γ
         → (∀{w'} → w ≺ w' → (Γ ⇒ A [ w' ] → ⊥) → Γ ⇒ C [ w ])
         → Γ ⇒ C [ w ]


   -- Core metric
   data Shape (Δ : MCtx) (w : W) : Set where
      s0 : Shape Δ w
      s1 : Shape Δ w → Shape Δ w
      s2 : Shape Δ w → Shape Δ w → Shape Δ w 
      s3 : Shape Δ w → Shape Δ w → Shape Δ w → Shape Δ w
      s□⇒ : ∀{A} 
          → ((∀{w'} → w ≺ w' → Δ ⇒ A [ w' ]) → Shape Δ w) → Shape Δ w
      s□⊢ : ∀{A} 
          → ((∀{w'} → w ≺ w' → Δ ⊢ A [ w' ]) → Shape Δ w) → Shape Δ w
      s◇⇒ : ∀{A}
          → (∀{w'} → w ≺ w' → Δ ⇒ A [ w' ] → Shape Δ w) → Shape Δ w
      s◇⊢ : ∀{A} 
          → (∀{w'} → w ≺ w' → Δ ⊢ A [ w' ] → Shape Δ w) → Shape Δ w
      s¬□⇒ : ∀{A} 
          → ((∀{w'} → w ≺ w' → Δ ⇒ A [ w' ] → ⊥) → Shape Δ w) → Shape Δ w
      s¬□⊢ : ∀{A} 
          → ((∀{w'} → w ≺ w' → Δ ⊢ A [ w' ] → ⊥) → Shape Δ w) → Shape Δ w
      s¬◇⇒ : ∀{A} 
          → (∀{w'} → w ≺ w' → (Δ ⇒ A [ w' ] → ⊥) → Shape Δ w) → Shape Δ w
      s¬◇⊢ : ∀{A} 
          → (∀{w'} → w ≺ w' → (Δ ⊢ A [ w' ] → ⊥) → Shape Δ w) → Shape Δ w
