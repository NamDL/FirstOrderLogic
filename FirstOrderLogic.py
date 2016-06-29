#!/usr/bin/python

import sys
import Queue
import heapq
import copy
import re
import inspect

KB=[]
variableList={}
goalProve=False
countStandard=0
   
class Clause:
   'Defines each square in the board'   
   def __init__(self,variableLength,name):
      self.variables={}
      self.variableLength = variableLength
      self.name=name;
      fact=[]
   def setVariables(self,oldVariable):
      self.variables=copy.deepcopy(oldVariable)
 

class Implication:
   'antecedant and consequent are an array of Clauses'
   def _init_(self):
      self.antecedant=[]
      self.consequent=[]
      isVisited=False
   def setVariables(self,antecedant,consequent,isFact):
      self.antecedant=copy.deepcopy(antecedant)
      self.consequent=copy.deepcopy(consequent)
      'If the isFact is set to TRUE, they no need to check for consequent'
      self.isFact=isFact
      
def makeClauses(result):
   listRet=[]
   queryList=result.split("&&")
   for x in queryList:
      varCount=0
      name=x.split("(")[0].strip()
      variables=x[:-2].split("(")[1].strip().split(",")
      for y in range(0,len(variables)):
         if variables[y].islower():
            varCount=varCount+1
         variables[y]=variables[y].strip()
      query=Clause(varCount,name)
      query.setVariables(variables)
      listRet.append(query)
   return listRet      
   
def makeKB(result):
   isFact=False
   anteceDantArray=[]
   consequentArray=[]
   if "=>" not in result:
      isFact=True
      consequentArray=makeClauses(result.split("=>")[0])
   else:
      anteceDantArray=makeClauses(result.split("=>")[0])
      consequentArray=makeClauses(result.split("=>")[1])
   implObj=Implication()
   implObj.setVariables(anteceDantArray,consequentArray,isFact)
   return implObj

def printKB():
   global KB
   for impl in KB:
      for x in impl.antecedant:
         print x.name,x.variables
      print " => "
      for x in impl.consequent:
         print x.name,x.variables


def printToFile(quest,clause,theta,fo):
   varList=[]
   for var in clause.variables:
      if var.islower():
         value=subst(theta,var)
         if value.islower():
            varList.append("_")
         else:
            varList.append(value)
      else:
         varList.append(var)         
   string=quest+": "+clause.name+"("+", ".join(varList)+")"
   'print string'
   fo.write(string)
   fo.write("\n")

def checkVariable(x):
   if type(x) is str:
      return x.islower()
   return False

def unify(x,y,theta):
   if theta==None:
      return None
   elif x==y:
      return theta
   elif checkVariable(x):
      return UnifyVar(x,y,theta)
   elif checkVariable(y):
      return UnifyVar(y,x,theta)
   elif isinstance(x,Clause) and isinstance(y,Clause):
      return unify(x.variables,y.variables, unify(x.name,y.name,theta))
   elif type(x) is list and type(y) is list:
      xRest=x[1:]
      yRest=y[1:]
      xFirst=x[0]
      yFirst=y[0]
      return unify(xRest,yRest,unify(xFirst,yFirst,theta))
   else:
      return None
                   
def UnifyVar(var,x,theta):
   if var in theta:
      return unify(theta[var],x,theta)
   elif x in theta:
      return unify(var,theta[x],theta)
   else:
      theta2=copy.deepcopy(theta)
      theta2[var]=x
      return theta2

'write a substitute function for substituting firt with value in theta recursievely'

def subst(theta,varList):
   if varList in theta:
      if theta[varList] in theta:
         return(subst(theta,theta[varList]))
      else:
         return theta[varList]
   else:
      return varList

def substClause(theta,clause):
   clause2=copy.deepcopy(clause)
   for i in range(0,len(clause.variables)):
      clause2.variables[i]=subst(theta,clause2.variables[i])
   return clause2

def FetchRulesForGoal(goal):
   retList=[]
   for impl in KB:
      impl.consequent[0].isVisited=False
      if impl.consequent[0].name==goal.name:
         retList.append(impl)
   return retList

def FOlBCASK(query,fo,proveCount):
   global KB
   return(FOLBCOR(query,{},fo,proveCount))

def FOLBCOR(goal,theta,fo,proveCount):
   global KB
   global goalProve
   global goalCause
   global goalASK
   'print "in OR with ",goal.name,goal.variables'
   goalCheck=False
   goalASK=True
   if goalProve:
      return
   printToFile("Ask",goal,theta,fo)
   i=0
   lengthGoalMatches= (len(FetchRulesForGoal(goal)))
   for impl in FetchRulesForGoal(goal):
      i=i+1
      impl=standardize(impl)
      'print "Calling Unisy with ",impl.consequent[0].name,impl.consequent[0].variables,theta'
      'print "Calling FOLBCAND with "'
      'print "ASK ",goal.name,goal.variables'
      'printToFile("ASK",goal,theta,fo)'
      for value in FOLBCAND(impl.antecedant,unify(impl.consequent[0],goal,theta),fo,goalASK):
         if value is not None:
            goalCheck=True
            goalASK=False
            impl.consequent[0].isVisited=True
            printToFile("True",goal,value,fo)
            yield value               
      'print goalASK,i,lengthGoalMatches-1,len(impl.antecedant)'
      if i<=(lengthGoalMatches-1) and goalASK and len(impl.antecedant)!=0:
         printToFile("Ask",goal,theta,fo)
      if impl.consequent[0].isVisited and goalASK and i<(lengthGoalMatches-1):
         printToFile("Ask",goal,theta,fo)
   if not goalCheck:
      if proveCount==0:
         goalProve=True
      printToFile("False",goal,theta,fo)
      impl.consequent[0].isVisited=True
      yield None     

def FOLBCAND(goal,theta,fo,goalASK):
   'print "In AND with theta= ",theta'
   global KB
   if theta is None:
      'print "returning with none"'
      'goalASK=True'
      yield None 
   elif len(goal)==0:
      'print "goal len==0, returning same ",theta'
      yield theta
   else:
      first=goal[0]
      rest=goal[1:]
      'print "calling OR with ",first.name,first.variables'
      'printToFile("Ask",first,theta,fo)'
      for val in FOLBCOR(substClause(theta,first),theta,fo,-1):         
         'printToFile("Ask",first,theta,fo)'
         'print "calling and with values ",val'
         '''if val is None:
               goalASK=True'''
         for val2 in FOLBCAND(rest,val,fo,goalASK):
            'print "yielding values",val2'
            '''if val2 is None:
               goalASK=True'''
            yield val2

def stripSpaces():
   for i in range(0,len(KB)):
      for j in range(0,len(KB[i].antecedant)):
         for k in range(0,len(KB[i].antecedant[j].variables)):
            KB[i].antecedant[j].variables[k]=KB[i].antecedant[j].variables[k].strip()
      for l in range(0,len(KB[i].consequent[0].variables)):
         KB[i].consequent[0].variables[l]=KB[i].consequent[0].variables[l].strip()
         

def standardize(implOld):
   global countStandard
   claList={}
   impl=copy.deepcopy(implOld)
   for i in range (0,len(impl.antecedant)):
      'print impl.antecedant[i].name'
      for j in range (0,len(impl.antecedant[i].variables)):
         if checkVariable(impl.antecedant[i].variables[j]):
            if impl.antecedant[i].variables[j] not in claList:
               implVariable=impl.antecedant[i].variables[j]
               newSTDVariable="x"+str(countStandard)
               'print impl.antecedant[i].variables[j],newSTDVariable'
               impl.antecedant[i].variables[j]=newSTDVariable
               countStandard=countStandard+1
               claList[implVariable]=newSTDVariable
               'print claList'
            else:
               impl.antecedant[i].variables[j]=claList[impl.antecedant[i].variables[j]]
   for k in range(0,len(impl.consequent[0].variables)):
      if checkVariable(impl.consequent[0].variables[k]):
         if impl.consequent[0].variables[k] in claList:
            impl.consequent[0].variables[k]=claList[impl.consequent[0].variables[k]]
            'print impl.consequent[0].variables[k],impl.consequent[0].name'
   return impl          
   

def printVariables():
   global variables
   print variableList
        
def main(fname,fo):
   result=[]
   finalResult=[]
   global KB
   with open(fname) as f:
       for line in f:
           result.append(line)
   goal=makeClauses(result[0])
   forEnd=int(result[1])
   for i in range(0,forEnd):
      KB.append(makeKB(result[i+2]))
   for i in goal:
      valueBCASK=FOlBCASK(i,fo,0)      
      next(valueBCASK)      
   if goalProve:
      fo.write("False")
      'print "False"'
   else:
      'print "True"'
      fo.write("True")
   'print "\n \n"'
   'printKB()'
   'printVariables()'

fo = open("output.txt", "a")
main(sys.argv[2],fo)
