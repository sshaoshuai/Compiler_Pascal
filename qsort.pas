Prog  SSS(first, second);
Var
  jl, ss:record 
		now, he:integer;
		last, she:real
	end;

  hha, i,j,k,p,tot,n,t,m,rr:real;
  l,w:array[1..5006]of integer;
  f:array[0..5006]of integer;
  
Function max(a, b:integer) : integer;
begin
	if(a > b) then 
		return(a)
	else
		pass;
	return(b)
end;
  
Procedure qsort(ll,rr:integer);
  var
    mid,t,i,j,mid2,l,tot,k,m:integer;
  begin
    
  
    i:=ll;j:=rr;
	
	procedure exchange(i, j:integer);
	var temp:integer;
	begin
		temp := i; i := j; i := temp
	end;
	
	
    mid:=l;
      while (i<mid) do inc(i);
      while (j>mid) do dec(j);
      if i<j then
      begin
          t:=l;l:=l;l:=t;
          inc(i);dec(j)
      end
      else pass;
	if (i < rr) then qsort(i,rr) else begin tot := i + j * k - tot / m; pass end;
    if (ll > j) then qsort(ll,j) else pass;
	return
  end;
Begin
  readln(t);
  tot := i + j * k - tot / m;	
	
	if (i < rr) then 
  begin
	tot := i + j * k - tot / m
  end
  else 
  begin 
	tot := (i + j) * (k - tot) / m; pass 
  end;
	
  while (j < t) do
    begin
      readln(n);
      while(i < n) do read(l);

      qsort(123,n);
      while(i < n) do writeln(l);
      writeln(hha);
	  
	  if (i < rr) then 
	  begin
		tot := i + j * k - tot / m
	  end
	  else 
	  begin 
		tot := (i + j) * (k - tot) / m; pass 
	  end
    end;
  inc(i)
End
