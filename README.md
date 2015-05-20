A port of Francois Pottier's inferno library from OCaml to Haskell.

See the
[paper](http://gallium.inria.fr/~fpottier/biblio/pottier_abstracts.html#pottier-elaboration-13)
for more information.

This translation to the world's finest imperative programming language is (so
far) fairly faithful. 

An example for core ML is in the file [test/Client.hs](test/Client.hs). This
file uses the library to implement a type inferencer as described in the
paper.

A slightly different example [test/G.hs](test/G.hs) elaborates a language with
optional type annotations to itself. It is called G because that is the letter
after F.

The interface to the library is contained in
[UnifierSig.hs](src/Language/Inferno/UnifierSig.hs) and 
[Solver.hs](src/Language/Inferno/Solver.hs).  The requirements of the
object language types are fairly small:

* The most important part of this interface is that it requires the definition
  of a shallow type.  This shallow type must be an instance of the classes
  Typeable, Traversable and Foldable as well as a new one called `ZipM`.  This
  last class compares two shallow types and throws an exception if they
  differ.

* The output type of the elaborator must also be a member of the `Output` type
  class.

Observations
------------
* I tried very hard to make the most literal translation that I could from
  OCaml to Haskell. This means that the Haskell code is more
  imperative than is idiomatic.
  
  
* One place this was a bit ridiculous was the treatment of fresh variable 
  generation.  The ML library can encapsulate a counter in a module, and
  generate fresh variables based on that "global" state. 
  
  The Haskell version avoids the easy `unsafePerformIO` solution and instead
  defines a freshness monad. That monad constraint means that the state can be
  passed around, marking where fresh variables are necessary.

* For a while, the monad that the library worked with was truly generic. i.e. 
  as long as it supported Freshness, References and Arrays. That means that
  this code would work in either ST or IO. But this generic version has a
  steep price, not only are the type signatures terribly complicated, but I was
  unable to find a generic implementation of hashtables.

  Therefore, the file SolverM.hs defines exactly the monad that we need, based
  on IO. All of the files in the [M](src/Language/Inferno/M/) subdirectory are
  specialized to this Monad. It could be changed to ST by editing SolverM.hs.  

* Haskell's lack of functors means that I had to resort to type
  parameterization throughout the library. That means that the interface types
  of the solver are parameterized by the input and output types.
  Insead of 
  
        exist :: (Variable -> Co a) -> Co (t, a)
  
  we have:
  
        exist :: forall t a. (Output t) =>
         (Var (Src t) -> M (Co t a)) -> M (Co t (t,a))
  
  I used type families instead of functional dependencies, so at least this
  function has 2 type arguments instead of 3.

* Bugs in the example code are very hard to debug! I spent much time trying to
  track down an error in my ZipM instance.

TODO
----
  
  - Break out parts such as `TRef`, `MonadEqRef`, `TUnionFind`, and
    `MonadFresh` into a separate project.

  - Replace exceptions with something else? Or figure out how to get the type
    inferencer to give better error messages at least?

(Planned) Extensions
------------------------
- monomorphic type annotations (done)
- recursive lets (need to be done)
- mixed-prefix unification
- polymorphic recursion
- type classes
- GADTs
- kinds
- higher-rank polymorphism

