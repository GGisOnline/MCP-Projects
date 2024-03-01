/***
    LINFO1122 - Méthodes de Conception de Programmes
    Devoir 3 - Vérification avec Dafny
    ================================================
    Automne 2023, Charles Pecheur

Pour ce troisième devoir, il vous est demandé de compléter, spécifier et de vérifier 
le programme Dafny ci-dessous.  

Il s'agit d'une implémentation de tri par fusion sur des tableaux. Vous devez implémenter 
la méthode `merge()`.  La méthode principale `sort()` est déjà implémentée.  
Plusieurs prédicats sont également fournis, utilisez-les pour vos spécifications.

Pour être valide, votre code doit pouvoir être vérifié par Dafny. 
- Implémentez la méthode `sort()`.
- Dans un premier temps, ne vous occupez pas du code de test (fonction 
`Main()`).  L'annotation `{:verify false}` court-circuite la vérification, 
vous pourrez l'enlever par la suite. 
- Ajoutez les spécifications nécessaires (requires, reads, modifies, fresh, 
invariants) pour résoudre toute les erreurs reportées par Dafny.  
- Complétez les spécifications des méthodes.  Travaillez progressivement, en apportant à 
chaque fois les corrections et ajouts nécessaires pour que la vérification 
réussisse.
- Quand vos spécifications seront complètes, activez la vérification de la 
fonction `Main()` (en supprimant le `{:verify false}`) et complétez
si nécessaire vos spécifications.  Enfin, vous pouvez compiler et exécuter 
votre programme (dans VS-Code, clic droit > Dafny > Run).

Idéalement, toutes vos spécifications doivent être vérifiables.  
Commentez et annotez comme suit celles qui ne le seraient pas:

    // FAILS: ensures world_is_enough()

Votre code sera votre rapport. Pensez à détailler les problèmes rencontrés
et les choix effectués quand cela est pertinent, sous forme de commentaires
dans le code.

Ce devoir est à remettre pour le **mercredi 20 décembre** sur Moodle.
***/



/***

Work 3 made by Group L : LECHAT Jérôme, LOUETTE Arthur & FRAIPONT Arthur

 */



predicate ordered(a: array<int>)
    /* `a[..]` est ordonné. */
    reads a
{
    forall i,j | 0 <= i < j < a.Length :: a[i] <= a[j]
}

predicate ordered_upto(a: array<int>, n: int)
    /* `a[..n]` est ordonné. */
    requires 0 <= n <= a.Length
    reads a
{
    forall i,j | 0 <= i <= j < n :: a[i] <= a[j]
}

predicate ordered_split(a1: array<int>, n1: int, a2: array<int>, n2: int)
    /* a1[..i1] <= a2[i2..] */
    requires 0 <= n1 <= a1.Length
    requires 0 <= n2 <= a2.Length
    reads a1, a2
{
    forall i1 | 0 <= i1 < n1 ::
        forall i2 | n2 <= i2 < a2.Length :: 
            a1[i1] <= a2[i2]
}

predicate same_elements(a1: array<int>, a2: array<int>)
    /* `a1[..]` et `a2[..]` contiennent les mêmes éléments. */
    reads a1, a2
{
    multiset(a1[..]) == multiset(a2[..])
}

method merge(a1: array<int>, a2: array<int>) returns (a: array<int>)
    /* fusionne deux tableaux ordonnés `a1` et `a2` en un seul tableau ordonné `a`. */
    requires a1 != null && a2 != null //@PRE : Tableaux non null
    requires ordered(a1) //@PRE : Tableau 1 trié
    requires ordered(a2) //@PRE : Tableau 2 trié

    ensures a.Length == a1.Length + a2.Length //@POST : Taille du tableau final = taille du tableau 1 et 2 fusionnée
    //ensures ordered(a) //@POST : Taille du tableau final trié --- [FAILS ordered(b) => Semble poser problème, fallait-il être encore plus récis ? Nous avons cherché pendant de longues heures mais aucune solution n'a été trouvée... 'a postcondition could not be proved on this return path']
    //ensures multiset(a[..]) == multiset(a1[..]) + multiset(a2[..]) //@POST : Le multiset du tableau final correspond à l'union des multisets de a1 et a2 --- [FAILS proof_multiset => Semble poser problème, fallait-il être encore plus récis ? Nous avons cherché pendant de longues heures mais aucune solution n'a été trouvée... 'a postcondition could not be proved on this return path']
{

    var i := 0;
    var j := 0;
    a := new int[a1.Length + a2.Length]; //on crée un nouveau tableau d'entiers de longueur a1 + a2

    while i < a1.Length && j < a2.Length
        //Invariant de boucle pour être sur que i et j restent bien dans les limites convenues
        invariant 0 <= i <= a1.Length && 0 <= j <= a2.Length
        invariant ordered_split(a1, i, a2, j)
        invariant multiset(a[..(i+j)]) == multiset(a1[..i] + a2[..j])
        
        // Decrease the number of unprocessed elements in each iteration
        decreases a1.Length - i + a2.Length - j 
    {
        if a1[i] <= a2[j] { //si élément à position i de a1 est plus petit/égal à élément à position j de a2
            a[i + j] := a1[i]; //on met à l'indice i + j l'élément a1[i] dans a
            i := i + 1; //on incrémente i de + 1
        } else { ////si élément à position i de a1 est plus grand à élément à position j de a2
            a[i + j] := a2[j]; //on met à l'indice i + j l'élément a2[j] dans a
            j := j + 1; //on incrémente j de + 1 
        }
    }

    //Gere les cas où il resterait des éléments de a1 ou a2
    while i < a1.Length
        //Invariant de boucle pour être sur que i reste bien dans les limites convenues
        invariant 0 <= i <= a1.Length
        // Decrease the number of unprocessed elements in a1
        decreases a1.Length - i 
    {
        a[i + j] := a1[i];
        i := i + 1;
    }

    //Gere les cas où il resterait des éléments de a1 ou a2
    while j < a2.Length
        //Invariant de boucle pour être sur que j reste bien dans les limites convenues
        invariant 0 <= j <= a2.Length
        // Decrease the number of unprocessed elements in a2
        decreases a2.Length - j 
    {
        a[i + j] := a2[j];
        j := j + 1;
    }
    
}








method sort(a: array<int>) returns (b: array<int>)
    /*  Retourne un tableau ordonné `b` contenant 
        les éléments de `a`. */

    requires a.Length >= 0 //@PRE : Tableaux non null
    
    decreases a.Length
    
    ensures a.Length == b.Length //@POST : La longueur des deux listes sont identiques
    ensures ordered(b) //@POST : Taille du tableau final trié --- [FAILS ordered(b) => Semble poser problème, fallait-il être encore plus récis ? Nous avons cherché pendant de longues heures mais aucune solution n'a été trouvée... 'a postcondition could not be proved on this return path'] 
    ensures same_elements(a, b) //@POST : La liste a et b contiennent bien les mêmes éléments 
{
    if a.Length <= 1 {
        b := a;
    } else {
        var m := a.Length/2;
        var a1 := new int[m];
        var a2 := new int[a.Length-m];
        forall i | 0 <= i < m { a1[i] := a[i]; }
        forall i | 0 <= i < a.Length-m { a2[i] := a[m+i]; }
        assert a1[..]+a2[..] == a[..];
        a1 := sort(a1);
        a2 := sort(a2);
        b := merge(a1, a2);
    }
}

/**
 * Tests
 */
method Main()
{
    var a := new int[][4,2,3,3,5,1];
    var b := sort(a);
    assert ordered(b);
    assert same_elements(a, b);

    print_array(a);
    print_array(b);
}

method print_array(a: array<int>)
{
    print "[ ";
    var i := 0;
    while i < a.Length
    {
        print a[i], " ";
        i := i+1;
    }
    print "]\n";
}