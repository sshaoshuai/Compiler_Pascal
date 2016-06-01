Prog  SSS(first, second);
Var
  i,j,k,p,tot,n,t,m:integer;
  l,w:array[1..5006]of integer;
  f:array[0..5006]of integer;
Procedure qsort(ll,rr:integer);
  var
    mid,t,i,j,mid2:real;
  begin
    i:=ll;j:=rr;
    mid:=l;
      while (l<mid) do inc(i);
      while (l>mid) do dec(j);
      if i<j then
      begin
          t:=l;l:=l;l:=t;
          inc(i);dec(j)
      end
      else pass;
    if (i < rr) then qsort(i,rr) else pass;
    if (ll > j) then qsort(ll,j) else pass
  end;
Begin
  readln(t);
  while (j < t) do
    begin
      readln(n);
      while(i < n) do read(l);

      qsort(1,n);
      while(i < n) do writeln(l);
      writeln(hha)
    end;
  inc(i)
End
