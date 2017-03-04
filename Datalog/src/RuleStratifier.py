'''
Created on Dec 18, 2014

@author: nando
'''

from Types import Predicate

def updateStratums(predicate_id, rule, stratums):
    # Find the current stratum for the current rule
    stratum_of_rule = 0
    for stratum_level, stratum in enumerate(stratums):
        for stratum_rule in stratum:
            if rule == stratum_rule:
                stratum_of_rule = stratum_level
                
    # Find the stratum it should be in
    new_stratum = 0
    found = False
    for stratum_level, stratum in enumerate(stratums):
        for stratum_rule in stratum:
            if stratum_rule.head.id == predicate_id:
                if stratum_level >= new_stratum:
                    new_stratum = stratum_level + 1
                found = True
                
    #TODO: Comprobar que en el stratum actual se puede colocar la regla sin problemas
    
    if found:
        stratums[stratum_of_rule].remove(rule)
        if len(stratums) <= new_stratum:
            stratums.append([rule])
        else:
            stratums[new_stratum].append(rule)
    
        
def stratifyRules(rulesTable):
    stratums = [rulesTable[:]]
    for rule in rulesTable:
        if rule.type == 1:
            if type(rule.body[0]) == Predicate and rule.body[0].negated:
                updateStratums(rule.body[0].id, rule, stratums)
            if len(rule.body) > 1 and type(rule.body[1]) == Predicate and rule.body[1].negated:
                    updateStratums(rule.body[1].id, rule, stratums)
        
        if rule.type == 2:
            if type(rule.body[1]) == Predicate and rule.body[1].negated:
                updateStratums(rule.body[1].id, rule, stratums)
            if len(rule.body) > 2 and type(rule.body[2]) == Predicate and rule.body[2].negated:
                updateStratums(rule.body[2].id, rule, stratums)

            
#     for level, stratum in enumerate(stratums):
#         print "LEVEL", level, ":"
#         for rule in stratum:
#             print "\t", rule.rule,
            
    return stratums
            
        
        