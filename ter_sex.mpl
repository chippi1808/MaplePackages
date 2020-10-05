globalvar:=[x,y,z]:

##########################
##csum(exp,var),cpro(exp,var)
##����������ֱ��exp����var�б��������ֻ���ͺͻ�
##These two functions return the cyclic sum and product of the input exp w.r.t. var, respectively.
##########################
csum:=proc(exp)
		local temp,var,temp1,temp2,tempexp,tempf,tempjg:
		if nargs=1 then
				var:=globalvar:
		else
				var:=args[2]:
		fi:
		temp:=nops(var):
		temp1:=[op(var),op(var)]:
		tempexp:=expand(exp):
		tempf:=unapply(tempexp,var):
		tempjg:=0:
		for temp2 from 1 to temp do 
				tempjg:=tempjg+tempf(op(temp2..temp2+temp-1,temp1)):
		od:
		return(tempjg):
end proc:

cpro:=proc(exp)
		local temp,var,temp1,temp2,tempexp,tempf,tempjg:
		if nargs=1 then
				var:=globalvar:
		else
				var:=args[2]:
		fi:
		temp:=nops(var):
		temp1:=[op(var),op(var)]:
		tempexp:=expand(exp):
		tempf:=unapply(tempexp,var):
		tempjg:=1:
		for temp2 from 1 to temp do 
				tempjg:=tempjg*tempf(op(temp2..temp2+temp-1,temp1)):
		od:
		return(tempjg):
end proc:

definef:=proc(n,ent)
		local temp,tn,var,d1,d2,d3,K,J,i,j,temp1,temp2,ti:
		if nargs=2 then
				var:=globalvar:
		else
				var:=args[3]:
		fi:
		if n<2 then
				print("ERROR, the degree must be larger than 1!"):
				return(ERROR):
		fi: 
		i:=ent[1]:
		j:=ent[2]:
		d1:=var[1]+var[2]+var[3]:
		d2:=var[1]*var[2]+var[2]*var[3]+var[3]*var[1]:
		d3:=var[1]*var[2]*var[3]:
		tn:=n-3*i:
		K:=floor(tn/2):
		J:=floor(tn/3):
		if (tn=2 and not(j=1)) or (tn=3 and not(j=1 or j=2)) then
				printf("ERROR, the %a is out of range of degree %d!",ent,n):
				return(ERROR):
		fi:
		ti:=0:
		if i>=0 and i<=floor(n/3) and j>=1 and j<=floor((tn+2)/2) and tn>=2 then
				if j=1 then
						temp1:=csum(var[1]^(tn-2)*(var[1]-var[2])*(var[1]-var[3]),var):
				else 
						if tn>=3 then
								if j=2 then
										temp1:=csum(var[1]^(tn-3)*(var[2]+var[3])*(var[1]-var[2])*(var[1]-var[3]),var):
								else
										if j<=K then
												temp1:=d1^(tn-2*j)*d2^(j-3)*((var[1]-var[2])*(var[2]-var[3])*(var[3]-var[1]))^2:
										else
												temp1:=csum((var[2]*var[3])^floor((tn-2)/2)*(var[2]+var[3])^(modp(tn,2))*(var[1]-var[2])*(var[1]-var[3]),var):
										fi:
								fi:
						fi:
				fi:
				temp1:=(var[1]*var[2]*var[3])^i*temp1:
				temp2:=unapply(expand(temp1),var):
				return(temp2(op(var))):
				return(temp1):
		else		
				printf("ERROR, the %a is out of range of degree %d!\n",ent,n):
				return(ERROR):
		fi: 
end proc:

#############
##������жԳ�������Ԫ���ȫ�Գƶ���ʽ�������������Schur��ʽ
##���룺exp--���жԳ�������Ԫ���ȫ�Գƶ���ʽ
##      var--��ѡ�����ޣ���Ĭ��exp������ԪΪ[x,y,z]
##                 ���У���ΪĬ��exp������Ԫ
##      ff--��ѡ�����У��򴫵ݳ�[[Schur���ţ�����[0,1]],[�����б���Ӧ��ϵ��]]
#############
schp:=proc(exp,varr,ff)
		local tempexp,var,tempf,temp1,tempfl,temp2,temp3,templ,temp11,temp21,temp31,n,sumf,tempcl:
		if nargs=1 then
				var:=globalvar:
		else
				var:=varr:
		fi:
		tempexp:=expand(exp):
		if not(type(tempexp,symmfunc(op(var)))) then
				print("ERROR, this polynomial is not symmetric!"):
				return(false):
		fi:
		if degree(tempexp,{op(var)})<>ldegree(tempexp,{op(var)}) then
				print("ERROR, this polynomial is not homonegeous!"):
				return(false):
		fi:
		tempf:=unapply(tempexp,var):
		if tempf(1,1,1)<>0 then
				print("ERROR, this polynomial doesn't vanish at (1,1,1)"):
				return():
		fi:
		sumf:=0:
		n:=degree(tempexp,{op(var)}):
		if n<2 then
				print("Error, the degree of this polynomial is smaller than 2!"):
				return(false):
		fi:
		tempfl:=[]:
		tempcl:=[]:
		while tempexp<>0 do
				temp1:=degree(tempexp,var[1]):
				temp11:=lcoeff(tempexp,var[1]):
				temp2:=degree(temp11,var[2]):
				temp21:=lcoeff(temp11,var[2]):
				temp3:=n-temp1-temp2:
				temp31:=lcoeff(temp21,var[3]):
				templ:=temp2-temp3+1:
				tempexp:=expand(tempexp-temp31*definef(n,[temp3,templ],var)):
				sumf:=sumf+temp31*F[n][temp3,templ]:
				tempfl:=[op(tempfl),[temp3,templ]]:
				tempcl:=[op(tempcl),temp31]:
		od:
		if nargs=3 then
				ff:=[tempfl,tempcl]:
				return(sumf):
		else
#				printf("The Schur Partition of %a is:\n",exp):
#				print(sumf):
#				printF(n,tempfl,var):
				return(sumf):
		fi:
end proc:

printF:=proc(n,ll,var)
		local temp:
		for temp in ll[1] do
				printf("F[%d]%a:=%a:\n",n,temp,definef(n,temp,var)):
		od:
end proc:

###############
##���룺����ʽpoly,ϵ���б�varl
##      ����������ƫ��v[1]>v[2]>...>v[n]��ʱ�������ϵ��lc�͸���Ԫ�����б�dg
##�����[lc,dg]
###############
lcdlist:=proc(poly,varl)
		local tempc1,tempdg,temppoly,tempvar,tempn:
		if nargs=1 then
				tempvar:=globalvar:
		else
				tempvar:=varl:
		fi:
		temppoly:=expand(exp):
		tempn:=nops(tempvar):
		tempdg:=[]:
		for tempc1 from 1 to tempn do
				tempdg:=[op(tempdg),degree(temppoly,tempvar[tempc1])]:
				temppoly:=lcoeff(temppoly,tempvar[tempc1]):
		od:
		return([temppoly,tempdg]):
end proc:

##########
##ternary sextics with symmetric zero.
##f=a*f1+b*f2+c*f3+d*f4+alpha*f5+beta*f6
##########

##########
##ter_sex: using the *** methods to try to prove the definiteness of the given polynomial
##	input : poly --any ternary sextics with symmetric zero
##  output: true-- poly is psd and the nonnegative summation of poly
##				  false--the procedure can not determine the definiteness of poly
##########
ter_sex:=proc(poly,varl)
		local tempjg,tempcflist,tempvar,temppoly:
		if nargs=1 then
				tempvar:=globalvar:
		else
				tempvar:=varl:
		fi:
		temppoly:=expand(exp):
		if not(type(temppoly,symmfunc(op(tempvar)))) then
				print("ERROR, this polynomial is not symmetric!"):
				return(false):
		fi:
		tempcflist:=coefflist(poly):
		if tempcflist[1]=0 then
				tempjg:=class1_dec(tempcflist):
		else
				tempjg:=false:
		fi:
		return(tempjg):
end proc:


##########
##coefflist:find the coefficients of [f1..f6]
##input : poly-- any ternary sextics with symmetric zero
##output : coefficients list [a,b,c,d,alpha,beta]
##########
coefflist:=proc(poly)
		local tempjg,tempschp,tempf,tempc1:
		tempjg:=[]:
		tempschp:=schp(poly):
		tempf:=[F[6][0,1], F[6][0,2], F[6][1,1], F[6][1,2], F[6][0,4], F[6][0,3]]:
		for tempc1 in tempf do
				tempjg:=[op(tempjg),coeff(tempschp,tempc1)]:
		od:
		return(tempjg):
end proc:

##########
##class1 : a=0
##########
##when a=0, this subfuction is called
class1_dec:=proc(coel)
		local tempb,tempc,tempd,tempalpha,tempbeta,tempdec,tempjg,tempf,temph,
			temptheta,tempepsilon,tempmu,tempomega,tempeta,tempxi,templambda,tempphi,tempgamma,
			temptau,temprho,temppsi,tempx0,tempc1:
		tempb:=coel[2]:
		tempc:=coel[3]:
		tempd:=coel[4]:
		tempalpha:=coel[5]:
		tempbeta:=coel[6]:
		temph:={}:
		tempjg:=0:
		if is(not(tempb>=0 and tempalpha>=0 and tempbeta+3*tempb+2*sqrt(tempb*tempalpha)>=0)) then
				return(false):
		fi:
		if tempb=0 then
				if tempalpha>=0 and tempbeta>=0 then
						if tempc=0 then
								if tempd>=0 then
										tempdec:=tempd*f4+tempalpha*f5+tempbeta*f6:
										tempf:={4,5,6}:
										tempjg:=1:
								fi:
						elif tempc>0 then
								if is(tempd+sqrt(tempc*tempalpha)>=0) then
										tempdec:=tempc*h1(sqrt(tempalpha/tempc))+(tempd+sqrt(tempc*tempalpha))*f4+tempbeta*f6:
										temph:={1}:
										tempf:={4,6}:
										tempjg:=2:
								fi:
						fi:
				fi:
		elif tempb>0 then
				temptheta:=tempc^2-12*tempb*tempd:
				if temptheta>=0 then
						tempepsilon:=(sqrt(temptheta)-tempc)/(6*tempb):
						if is(tempepsilon<0) then
								if tempc>0 and tempd>0 then
										tempdec:=tempb*h2(0,sqrt(tempalpha/tempb),0)+tempc*f3+tempd*f4+(3*tempb+tempbeta+2*sqrt(tempb*tempalpha))*f6:
										temph:={2}:
										tempf:={3,4,6}:
										tempjg:=3:
								fi:
						else
								tempmu:=(2*sqrt(temptheta)+tempc)/(6*tempb):
								if tempmu<0 then
										if 3*tempb+tempbeta>=0 then
												tempdec:=tempb*h2(-tempc/(4*tempb),0,0)+(tempd-tempc^2/(16*tempb))*f4+tempalpha*f5+(3*tempb+tempbeta)*f6:
												temph:={2}:
												tempf:={4,5,6}:
												tempjg:=4:
										else
												tempdec:=tempb*h2(-tempc/(4*tempb),sqrt(tempalpha/tempb),0)+(tempd-tempc^2/(16*tempb))*f4+(3*tempb+tempbeta+2*sqrt(tempb*tempalpha))*f6:
												temph:={2}:
												tempf:={4,6}:
												tempjg:=5:
										fi:
								else
										tempomega:=tempalpha/(2*tempb)-tempepsilon^2*tempmu:
										if tempomega>=0 then
												if is(3*tempb+tempbeta>=0) then
														tempdec:=tempb*h2(tempepsilon,0,0)+2*tempb*tempmu*h1(tempepsilon)+2*tempb*tempomega*f5+(3*tempb+tempbeta)*f6:
														temph:={1,2}:
														tempf:={5,6}:
														tempjg:=6:
												else
														tempdec:=tempb*h2(tempepsilon,sqrt(2*(tempepsilon^2*tempmu+tempomega))-sqrt(2*tempepsilon^2*tempmu),sqrt(2*tempmu))+(3*tempb+tempbeta+2*sqrt(tempb*tempalpha))*f6:
														temph:={2}:
														tempf:={6}:
														tempjg:=7:
												fi:
										fi:
								fi:
						fi:
				else
						if tempalpha>=0 then
								templambda:=-temptheta/(12*tempb^2):
								tempphi:=(54*tempb^2*tempalpha-18*tempb*tempc*tempd+tempc^3)/(108*tempb^3):
								tempgamma:=sqrt((4*templambda^3+27*tempphi^2)/108):
								tempx0:=(tempgamma-tempphi/2)^(1/3)-(tempgamma+tempphi/2)^(1/3)-tempc/6/tempb:
								if factor(subs(x=tempx0,2*tempb*x^3+tempc*x^2+2*tempd*x+tempalpha))<>0 then
										print(factor(subs(x=tempx0,2*tempb*x^3+tempc*x^2+2*tempd*x+tempalpha))):
										error "wrong x0":
								fi:
								temptau:=sqrt(-tempx0):
								temprho:=(2*tempb*temptau^2-tempc)/(4*tempb):
								temppsi:=sqrt(temptau^4+tempd/tempb-tempc*temptau^2/(2*tempb)):
								if temptau=0 then
										if tempbeta+3*tempb>=0 then
												tempjg:=8:
												tempdec:=tempb*h2(temprho,0,0)+2*tempb*temptau^2*h1(temptau)+tempb*(temppsi^2-temprho^2)*f4+(3*tempb+tempbeta)*f6:
												temph:={1,2}:
												tempf:={4,6}:
										fi:
								else
										tempjg:=9:
										tempdec:=tempb*h2(temprho,sqrt(2)*temptau*(temppsi-temprho),sqrt(2)*temptau)+tempb*(temppsi^2-temprho^2)*f4+(3*tempb+tempbeta+2*sqrt(tempb*tempalpha))*f6:
										temph:={2}:
										tempf:={4,6}:
								fi:
								
						fi:
				fi:
		fi:
		if tempjg=0 then
				print("The polynomial is not psd!"):
				return(false):
		else
				if has(temph,2) then
						tempf:=`union`(tempf,{2,3,4,5,6}):
				else 
						for tempc1 in tempf do
								if coeff(tempdec,cat(f,tempc1))=0 then
										tempf:=`minus`(tempf,{tempc1}):
								fi:
						od:
						if has(temph,1) then
								tempf:=`union`(tempf,{3,4,5}):
						fi:
				fi:
				print("This polynomial is psd! It can be decomposed as",tempjg):
				print(tempdec):
				print("in which"):
				for tempc1 in temph do
						print(hfunlist[tempc1]):
				od:
				for tempc1 in tempf do
						print(ffunlist[tempc1]):
				od:
				return(true):
		fi:
end proc:

hfunlist:=[h1(u)=f3-u*f4+u^2*f5,h2(u,v,w)=f2+(w^2-4*u)*f3+(u^2-u*w^2)*f4+(u*w+v)^2*f5-(2*u*w+2*v+3)*f6]:
ffunlist:=[f1=Sum(x^4*(x-y)*(x-z)),f2=Sum(x^3*(y+z)*(x-y)*(x-z)),f3=x*y*z*Sum(x*(x-y)*(x-z)),f4=x*y*z*Sum((y+z)*(x-y)*(x-z)),f5=Sum((y*z)^2*(x-y)*(x-z)),f6=Product((x-y)^2)]:
