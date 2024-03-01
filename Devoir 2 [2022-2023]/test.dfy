datatype Tree = Nil | Node(left: Tree, val: int, right: Tree) 
method insert(t: Tree, i: int)  returns(t': Tree) 
{
   if t == Nil { return Node(Nil,i,Nil); }
    if t.val < i { 
      var r := insert(t.right,i);
      t' := Node(t.left,t.val,r);  
    }else if t.val > i {
       var l := insert(t.left, i);
       t' := Node(l,t.val,t.right);
    }
    return t';
}

method Main(){
    var t := insert(Nil, 5);
    var c := insert(t,3);
    var v := insert(c, 6);
    print v, "\n";

}
