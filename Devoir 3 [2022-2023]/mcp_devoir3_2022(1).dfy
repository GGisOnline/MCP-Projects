/***
    LINFO1122 - Méthodes de Conception de Programmes
    Devoir 3 - Vérification avec Dafny
    ================================================
    Automne 2022, Charles Pecheur

Pour ce troisième devoir, il vous est demandé de spécifier et de vérifier 
le programme Dafny ci-dessous.  Il s'agit d'une classe qui implémente une
file de priorité (priority queue).  

Pour être valide, votre code doit pouvoir être vérifié par Dafny. 
Vous pouvez procéder comme suit:

- Dans un premier temps, ne vous occupez pas du code de test (fonction 
`Main()`).  La pré-condition `requires false` court-circuite la vérification, 
vous pourrez l'enlever par la suite. 
- Définissez l'invariant de représentation `ok()`.  La fonction d'abstraction 
`abs()` est déjà donnée.
- Ajoutez les spécifications nécessaires (requires, reads, modifies, fresh, 
invariants) pour résoudre toute les erreurs reportées par Dafny.
- Complétez les spécifications des méthodes petit à petit, en apportant à 
chaque fois les corrections et ajouts nécessaires pour que la vérification 
réussisse.
- Quand vos spécifications seront complètes, activez la vérification de la 
fonction `Main()` (en supprimant le `assert false`) et complétez
si nécessaire vos spécifications.  Enfin, vous pouvez compiler et exécuter 
votre programme (dans VS-Code, clic droit > Compile and Run).

Idéalement, toutes vos spécifications doivent être vérifiables.  Pensez à 
commenter et à annoter comme suit celles qui ne le seraient pas:

    // FAILS: ensures world_is_enough()

Votre code sera votre rapport. Pensez à détailler les problèmes rencontrés
et les choix effectués quand cela est pertinent, sous forme de commentaires
dans le code.

Ce devoir est à remettre pour le **vendredi 23 décembre** sur Moodle.
***/

/** Made by : LECHAT Jérôme (50351800) & SWIERZEWSKI Cezary (11141800)
* Notes : We had no really difficulties until we had to work on the insert fun which was really tough to make... 
* unfortunately this work is not 100% finished but we gave it all to make it work **/


predicate ordered(a: seq<int>)      // in decreasing order
{
    forall i,j | 0 <= i < j < |a| :: a[i] >= a[j]
}

predicate is_min(e: int, m: multiset<int>)      // e is the minimum in m
{
    e in m && forall e' | e' in m :: e <= e'
}

/**
 * A priority queue of integer values, represented as an ordered array,
 * with minimal value at the end.  The capacity (length of the array) is
 * set initially but increases dynamically when needed. 
 */
class PriorityQueue {
    var elems : array<int>;     // elements in decreasing order
    var size : int;             // number of elements in the queue

    /**
     * Create a queue with initial capacity {n}
     */
    constructor (n: int)
        requires n > 0
        ensures ok()
        ensures abs() == multiset([])
        ensures fresh(elems)
    {
        this.elems := new int[n];
        this.size := 0;
    }

    /**
     * Abstraction: a queue is a multiset (bag) of its elements 
     */
    function abs(): multiset<int>
        requires ok()
        reads this, elems
        ensures forall e | e in elems[..size] :: e in abs()
        ensures |abs()| == size
    {
        multiset(elems[..size])
    }

    /**
     * Representation invariant
     */
    predicate ok()
        reads this, elems
    {   
         0 <= size < elems.Length && 
         ordered(elems[..size])
    }

    /**
     * Return the minimal element in the queue.  Does not modify the queue.
     */
    method peek_min() returns (m: int)
        // TODO: specify
        requires ok()
        requires size > 1

        ensures ok()
        ensures is_min(m, abs())
        ensures elems == old(elems)
    {
        return elems[size-1];
    }

    /**
     * Remove and return the minimal element in the queue.
     */
    method get_min() returns (m: int)
        // TODO: specify
        modifies this, elems
        requires ok()
        requires size > 1

        ensures ok()
        //ensures is_min(m, abs())
        ensures elems == old(elems)

    {
        m := elems[size-1];
        size := size - 1;
    }

    /**
     * Resize the queue to a larger capacity.  The content of the queue is preserved.
     */
    method resize()
        // TODO: specify
        modifies this, elems
        requires ok()

        //ensures ok()
        //ensures elems.Length == elems.Length * 2
        //ensures forall i | 0 <= i <= old(size) :: elems[i] == old(elems[i])
    {
        var len := elems.Length * 2;
        var newelems := new int[len];
        var i := 0;
        while i < size
            modifies newelems
            // TODO: invariants
            invariant 0 <= i <= size
            invariant forall k | 0 < k < i :: newelems[k] == elems[k]
        {
            newelems[i] := elems[i];
            i := i + 1;
        }
        elems := newelems;
    }

    /**
     * Insert element {e} in the queue, with resizing if needed.
     */
    method insert(e: int)
        // TODO: specify
        modifies this, elems
        requires ok()
        requires 1 < size < elems.Length
        
        //ensures ok()

    {
        if size == elems.Length {
            resize();
            assert elems.Length > old(elems.Length);
            assert old(elems.Length) == size;
            assert elems.Length > size;
        }
        assert elems.Length > size;
        insert'(e);
    }

    /**
     * Insert element {e} in the queue, with available capacity.
     */
    method insert'(e: int)
        // TODO: specify
        modifies this, elems
        requires ok()
        requires size > 1

        //ensures ok()
        ensures size == old(size) + 1
    {
        var i := size;
        elems[i] := e;
        size := size+1;

        while i > 0 && (elems[i] > elems[i-1])
            modifies elems
            // TODO: invariants
            invariant 0 <= i
        {
            elems[i-1], elems[i] := elems[i], elems[i-1];
            i := i - 1;
        }
    }
}

/**
 * Tests
 */
method Main()
{
    var q := new PriorityQueue(2);
    q.insert(3);
    q.insert(2);
    q.insert(1);
    q.insert(2);
    assert q.abs() == multiset([1, 2, 2, 3]);
    assert is_min(1, q.abs());

    var a := q.get_min();
    var b := q.get_min();
    var c := q.get_min();
    var d := q.get_min();
    assert a <= b <= c <= d;
    assert a+b+c+d == 8;

    print "[", a, ", ", b, ", ", c, ", ", d, "]\n";
}
