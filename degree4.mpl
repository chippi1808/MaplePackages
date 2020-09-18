print("==================================================");
print("prove4");
print("Chuong trinh duoc viet boi Nguyen Quoc Anh");
print("Day la mot chuong trinh ma nguon mo. (Open source code.)");
print("bdtilove@live.com");
print("[[[[3.0]]]]");
print("Copyright(C) 2013-2016");
print("[xprove4,yprove4]");
print("==================================================");
######################################################################
sgm:=proc(expr)
   local rap,ex2,ex3,ex:
      rap:={a=b,b=c,c=a}:     
   ex2:=subs(rap,expr):
   ex3:=subs(rap,ex2):
   ex:=expr+ex2+ex3:
   RETURN(ex)
end:
######################################################################
pro:=proc(expr)
   local rap,ex2,ex3,ex:
      rap:={a=b,b=c,c=a}:     
   ex2:=subs(rap,expr):
   ex3:=subs(rap,ex2):
   ex:=expr*ex2*ex3:
   RETURN(ex)
end:
######################################################################
prove4:=proc(ineq)
  local exp,i,sj,ff,tt,ff1,g,f:
  if whattype(ineq)= `=` then print("This is not an inequality!") else
  g:=rhs(ineq)-lhs(ineq):f:=convert(g,`+`):sj:=time():exp:={}:tt:=0:ff1:=unapply(f,a,b,c):
  for i from 2 to nops([op(expand(numer(f)))]) do  
	if degree([op(expand(numer(f)))][i]/subs(a=1,b=1,c=1,[op(expand(numer(f)))][i]))<>degree([op(expand(numer(f)))][1]/subs(a=1,b=1,c=1,[op(expand(numer(f)))][1])) then tt:=tt+1:fi:od:
        
        if     tt>0 then  print("ERROR, this polynomial is not homonegeous!"):
        elif   tt=0 and nops(expand({ff1(a,b,c),ff1(a,c,b) ,ff1(b,c,a),ff1(c,a,b),ff1(c,b,a),ff1(b,a,c)}))>2 then print("ERROR,This form is not circle symmetric!")
        elif   tt=0 and  nops(expand({ff1(a,b,c),ff1(b,c,a),ff1(c,a,b)}))=1 then if type(f,symmfunc(a,b,c)) then print("This is a symmetric polynomial!"):check1(ineq):else print("This is a cyclic symmetric polynomial!"):check2(ineq):fi:fi:fi:
end:
######################################################################
solve01:=proc(ff1)
 local m,n,p,g,gg:
   m:=coeff(subs({a=a,b=1,c=1},ff1),a^4);
   n:=coeff(subs({a=a,b=1,c=0},ff1),a^2);
   p:=coeff(subs({a=a,b=1,c=0},ff1),a^3);
   g:=coeff(subs({a=a,b=0,c=1},ff1),a^3);
   if subs({a=a,b=a,c=a},ff1)=0 and 3*m*(m+n)-p^2-p*g-g^2>=0 and m>0 and p^2+p*g+g^2<>0 then 
	 gg:=sgm((3*m*(a^2-b^2)+(p-g)*a*b-(2*p+g)*b*c+(p+2*g)*c*a)^2/(18*m))+sgm((3*m*(m+n)-p^2-p*g-g^2)*((p-g)*a*b-(2*p+g)*b*c+(p+2*g)*c*a)^2/(18*m*(p^2+p*g+g^2))):
   else print("Cant give a solution."):fi;
end:
######################################################################
solve02:=proc(ff1)
  local k,l,o,ff7,ff6,Mm,i,j,gg:
  ff7:=sgm((k*a+l*b+o*c)^4);
  Mm:=solve(subs(a=1,b=1,c=1,{op(collect(ff1-ff7,[a,b,c],distributed))}),{k,l,o});
  gg:=remove(hastype, {Mm}, {And(complexcons, Not(realcons)), specfunc(anything, RootOf)}); 
  if gg<>{} then subs(gg[1], ff7) else print("Cant give a solution."):fi
end:
######################################################################
solve03:=proc(ff2)
 local m1,m2,m3,m4,m5,deg2,g,amu4,amu3b,amu3c,amu2bmu2,amu2bc,gg:
 m1 := simplify(coeff(subs({a = a, b = 1, c = 1}, ff2), a^4)); 
 m2 := simplify(coeff(subs({a = a, b = 1, c = 0}, ff2), a^2)); 
 m3 := simplify(coeff(subs({a = a, b = 1, c = 0}, ff2), a^3)); 
 m4 := simplify(coeff(subs({a = a, b = 0, c = 1}, ff2), a^3)); 
 m5 := simplify(coeff(subs({a = a, b = 1, c = 1}, ff2), a^2)-2*m2);
 amu4 :=(x^2+y^2+z^2);
 amu3b :=2*(x*m+z*p+y*n);
 amu3c :=2*(x*p+z*n+y*m);
 amu2bmu2 :=(2*x*y+2*y*z+2*z*x+m^2+n^2+p^2);
 amu2bc := 2*(x*n+m*p+z*m+n*p+y*p+m*n);
 g := sgm((x*a^2+y*b^2+z*c^2+m*a*b+n*b*c+p*c*a)^2);
 deg2 := solve({x=1,amu2bc = m5, amu3b = m3, amu3c = m4, amu4 = m1, amu2bmu2 = m2}, {m, n, p, x, y, z});
 gg:=remove(hastype, {deg2}, {And(complexcons, Not(realcons)), specfunc(anything, RootOf)}); 
  if gg<>{} then subs(gg[1], g) else print("Cant give a solution."):fi:
 end:
######################################################################
solve04:=proc(ff)
 local k,l,ff7,ff5,Mm,gg:
 ff7:=k*(sgm(a^2)-l*sgm(a*b))^2;
 Mm:=solve(subs(a=1,b=1,c=1,{op(collect(ff-ff7,[a,b,c],distributed))}),{k,l});
 gg:=remove(hastype, {Mm}, {And(complexcons, Not(realcons)), specfunc(anything, RootOf)}); 
 if gg<>{} then subs(gg[1], ff7) else print("Cant give a solution."):fi:
end:
######################################################################
check1:=proc(ineq)
 local ff1;
 ff1:=convert(rhs(ineq)-lhs(ineq),`+`);
   if solve(subs(b=1,c=1,ff1)>=0,a)=a and solve(subs(b=0,c=0,ff1)>=0,a)=a then print("This inequality is true! Try to solving: "):solve01(ff1),solve02(ff1),solve03(ff1),solve04(ff1); 
      else print("This inequality is false!"):fi:
end:   
######################################################################
check2:=proc(ineq)
 local m,r,p,q,s,ff2,ff1:
   ff1:=convert(rhs(ineq)-lhs(ineq),`+`);
   m:=coeff(subs({a=a,b=1,c=1},ff1),a^4);
   ff2:=expand(ff1/m);
   r:=coeff(subs({a=a,b=1,c=0},ff2),a^2);
   p:=-coeff(subs({a=a,b=1,c=0},ff2),a^3);
   q:=-coeff(subs({a=a,b=0,c=1},ff2),a^3);
   s := simplify(coeff(subs({a = a, b = 1, c = 1}, ff2), a^2)-2*r);
   if s>=p+q-r-1 and s<=2*(r+1)+p+q-p^2-p*q-q^2 then print("This inequality is true! Try to solving: "):solve01(ff1),solve02(ff1),solve03(ff1),solve04(ff1);
   else print("This inequality is false!"):fi:
end:
