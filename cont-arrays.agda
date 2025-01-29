open import Data.Product using (Σ; proj₁; proj₂; _×_; _,_)

infixl 1  _◃_

-- Container
record Con : Set₁ where
  constructor _◃_ 
  field
    S : Set
    P : S → Set

-- Container Morphism
record Mor (A B : Con) : Set where
  constructor _◃_
  open Con
  field
    S : A .S → B .S
    P : ∀ {a} → B .P (S a) → A .P a

variable
  X Y Z : Set
  s p q r : Con

data _⊎_ (A B : Set) : Set  where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

_⊕_ : Con → Con → Con
(A ◃ B) ⊕ (C ◃ D) = A ⊎ C ◃ λ { (inl a) → B a; (inr c) → D c } 

_⊗_ : Con → Con → Con
(A ◃ B) ⊗ (C ◃ D) = A × C ◃ λ (a , c) → B a × D c

_×ᶜ_ : Con → Con → Con
(A ◃ B) ×ᶜ (C ◃ D) = A × C ◃ λ (a , c) → B a ⊎ D c

Π : (A : Set) → (A → Set) → Set
Π A B = (a : A) → B a

Ar : Con → Set → Set
Ar (A ◃ B) X = Π A B → X 

-- Functoriality of Ar in shapes
fmap : ∀ {A B} → Mor A B → Ar A X → Ar B X
fmap m f = λ z → f (λ a → m .Mor.P (z (m .Mor.S a)))
    
-- Functoriality of Ar in elements
map : (X → Y) → Ar s X → Ar s Y
map f a i = f (a i)

K : X → Ar s X
K x i = x

zipWith : (X → Y → Z) → Ar s X → Ar s Y → Ar s Z
zipWith _⊞_ a b i = a i ⊞ b i

nest : Ar (s ⊕ p) X → Ar s (Ar p X)
nest a i j = a λ { (inl ss) → i ss; (inr ps) → j ps}

unnest : Ar s (Ar p X) → Ar (s ⊕ p) X
unnest a ij = a (λ i → ij (inl i)) (λ j → ij (inr j))

-- XXX: not sure that this should be called transpose
transpose : Ar (s ⊕ p) X → Ar (p ⊕ s) X
transpose a sp = a λ { (inl i) → sp (inr i) ; (inr j) → sp (inl j) } 

-- Generalised Kronecker product
kron : Ar s X → Ar p Y → Ar (s ⊕ p) (X × Y)
kron a b = unnest λ i j → a i , b j

-- Non-blocked matrix multiplication with on generalised shapes.
module Naive
  --(sum : ∀ {X s} → (X → X → X) → X → Ar s X → X)
  (sum : (Z → Z → Z) → Z → Ar p Z → Z)
  (_⊠_ : X → Y → Z) (ε : Z) (_⊞_ : Z → Z → Z)
  (let infixl 10 _⊠_; _⊠_ = _⊠_) where
  
  _∘_  : Ar (s ⊕ p) X → Ar (p ⊕ q) Y → Ar (s ⊕ q) Z
  a ∘ b = 
    unnest λ i j → sum _⊞_ ε λ k → nest a i k ⊠ nest b k j

data ⊥ : Set where
record ⊤ : Set where
  constructor tt

𝟘 : Con
𝟘 = ⊥ ◃ λ ()

𝟙 : Con
𝟙 = ⊤ ◃ λ _ → ⊤

Pi : Con → Set
Pi (A ◃ B) = Π A B

-- Definition of *inductive* container reshapes
module Reshapes where
  
  data Reshape : Con → Con → Set₁ where
    eq  : Reshape s s 
    _∙_ : Reshape p q → Reshape s p → Reshape s q 
    _⊞_ : Reshape s p → Reshape q r → Reshape (s ⊕ q) (p ⊕ r)
    lassoc : Reshape (s ⊕ (p ⊕ q)) ((s ⊕ p) ⊕ q)
    rassoc : Reshape ((s ⊕ p) ⊕ q) (s ⊕ (p ⊕ q))
    swap : Reshape (s ⊕ p) (p ⊕ s)
    lneut : Reshape s (𝟘 ⊕ s)
    rneut : Reshape (𝟘 ⊕ s) s

  rev : Reshape s p → Reshape p s
  rev eq = eq
  rev (r ∙ r₁) = rev r₁ ∙ rev r
  rev (r ⊞ r₁) = rev r ⊞ rev r₁
  rev lassoc = rassoc
  rev rassoc = lassoc
  rev swap = swap
  rev lneut = rneut
  rev rneut = lneut

  _⟨_⟩ : Pi s → Reshape p s → Pi p
  i ⟨ eq ⟩ = i
  i ⟨ r ∙ r₁ ⟩ = (i ⟨ r ⟩) ⟨ r₁ ⟩
  (i ⟨ r ⊞ r₁ ⟩) (inl x) = ((λ a → i (inl a)) ⟨ r ⟩) x
  (i ⟨ r ⊞ r₁ ⟩) (inr x) = ((λ a → i (inr a)) ⟨ r₁ ⟩) x
  (i ⟨ lassoc ⟩) (inl x) = i (inl (inl x))
  (i ⟨ lassoc ⟩) (inr (inl x)) = i (inl (inr x))
  (i ⟨ lassoc ⟩) (inr (inr x)) = i (inr x)
  (i ⟨ rassoc ⟩) (inl (inl x)) = i (inl x)
  (i ⟨ rassoc ⟩) (inl (inr x)) = i (inr (inl x))
  (i ⟨ rassoc ⟩) (inr x) = i (inr (inr x))
  (i ⟨ swap ⟩) (inl x) = i (inr x)
  (i ⟨ swap ⟩) (inr x) = i (inl x)
  (i ⟨ lneut ⟩) sp = i (inr sp)
  (i ⟨ rneut ⟩) (inr x) = i x

  reshape : Reshape s p → Ar s X → Ar p X
  reshape r a i = a (i ⟨ r ⟩)

-- Neils observation that Ar is a Yoneda embedding.
module Yoneda where
  open import Agda.Builtin.Equality
  -- Covariant
  Yon : Set → (Set → Set)
  Yon X A = X → A

  Ar′ : Con → Set → Set
  Ar′ C = Yon (Pi C)

  _ : ∀ {A B} → Ar′ (A ◃ B) X ≡ Ar (A ◃ B) X
  _ = refl


-- Induction over array shapes using a universe construction
module Univ where
  open import Data.Nat
  open import Data.Fin
  
  data S : Set₁
  El : S → Con

  data S where
    ι : S
    _⊗′_ : S → S → S

  El (ι ) = ℕ ◃ Fin
  El (c ⊗′ d) = El c ⊕ El d

  postulate
    mul : X → Y → Z
    sum : Ar s Z → Z

  _⊕ⁱ_ : Pi s → Pi p → Pi (s ⊕ p) 
  (i ⊕ⁱ j) (inl i′) = i i′
  (i ⊕ⁱ j) (inr j′) = j j′

  tile : ∀ {s p q} → Ar (El ((s ⊗′ p) ⊗′ q)) X → Ar (El (s ⊗′ (p ⊗′ q))) X
  tile a ix = a foo
    where foo : _
          foo (inl (inl i)) = ix (inl i)
          foo (inl (inr j)) = ix (inr (inl j))
          foo (inr k) = ix (inr (inr k))

  matv-canon : ∀ {s } → Ar (El (s ⊗′ ι )) X → Ar (El (ι )) Y → Ar (El s) Z 
  matv-canon m v = λ i → sum λ k → mul (m (i ⊕ⁱ k)) (v k)


  matv : ∀ {s } → Ar (El (s ⊗′ ι)) X → Ar (El (ι )) Y → Ar (El s) Z
  matv {s = ι }     m v = matv-canon {s = ι } m v
  matv {s = s ⊗′ p} m v = unnest (map (λ a → matv {s = p} a v)
                                      (nest (tile {s = s}{p}{ι}  m)))



-- This is an observation that we can acheive array
-- encoding via interpreting A-fold tensor product
-- of the (A ▹ B) container.  This is not very surprising,
-- as A-fold tensor product is a tabulated function Π A B.
module Diamond where
  open import Agda.Builtin.Equality
  open import Function

  ⟦_⟧ : Con → Set → Set
  ⟦ A ◃ B ⟧ X = Σ A λ a → B a → X

  ⨂ : Con → Con → Con
  ⨂ (A ◃ B) (C ◃ D) = ⟦ A ◃ B ⟧ C ◃ λ (a , f) → Π (B a) (D ∘ f)

  open Con
  to : Ar s X → ⟦ ⨂ (⊤ ◃ const (s .S)) s ⟧ X
  to a  = (tt , id) , a

  from : ⟦ ⨂ (⊤ ◃ const (s .S)) s ⟧ X → Ar s X
  from ((tt , f) , a) i = a (λ a₁ → i (f a₁))
  

-- Here we use our definitions to compute simple matmul.
module Example where
  open import Data.Nat
  open import Data.Fin using (Fin; zero; suc)
  open import Data.Vec as V
  
  Sg : ℕ → Con
  Sg n = ⊤ ◃ λ _ → Fin n
  
  Scal : Set → Set
  Scal X = Ar 𝟘 X
  
  Vect : ℕ → Set → Set
  Vect n X = Ar (Sg n) X
  
  Mat : (m n : ℕ) (X : Set) → Set
  Mat m n X = Ar (Sg m ⊕ Sg n) X
  
  m-vec : ∀ {m n} → Mat m n X → Vec (Vec X n) m
  m-vec a = tabulate λ i → tabulate λ j → a λ { (inl _) → i; (inr _) → j }

  vec-m : ∀ {m n} → Vec (Vec X n) m → Mat m n X
  vec-m m i = lookup (lookup m (i (inl tt))) (i (inr tt))

  vec-sum : ∀ {m n} → Vec (Vec ℕ n) m → ℕ
  vec-sum v = sum (V.map sum v)

  vect-vec : ∀ {n} → Vect n X → Vec X n
  vect-vec v = tabulate λ i → v λ _ → i

  vect-sum : ∀ {n} → (ℕ → ℕ → ℕ) → ℕ → Vect n ℕ → ℕ
  vect-sum op e v = foldr′ op e (vect-vec v) 

  test : Vec (Vec ℕ 3) 2
  test = let
            mm = Naive._∘_ vect-sum _*_ 0 _+_
            a = (vec-m ((1 ∷ 2 ∷ []) ∷ (3 ∷ 4 ∷ []) ∷ [])) 
            b = (vec-m ((1 ∷ 2 ∷ 3 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ []))
         in m-vec (mm a b)



