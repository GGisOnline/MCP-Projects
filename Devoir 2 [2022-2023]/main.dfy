type HashSet = array<List>
datatype List = Nil | Cons(string, List)


method create(n: int) returns (a: HashSet)
    requires n >= 0 //PRE
    ensures fresh(a) //POST

    {
        a := new List[n] ;
    }
 

method isin(s: string, a: HashSet) returns (result: bool) {
    
    var size := counter(a);

    if size == 0 {
        result := false;
    } else {
        //TODO
    }

}


method add(a: HashSet, s: string) {
    //TODO
}

method remove(a: HashSet, s: string) {
    //TODO
}


//Counter method
method counter(a: HashSet) returns (count: int){
    count := a.Length ;
}





method Main() {
    var test := create(5);
    print(test.Length);

    var test1 := counter(test);
    var test2 := isin("ddfs", test);

    print (test1);
    print (test2);
}