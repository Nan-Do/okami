'''
Created on Aug 5, 2013

@author: nando
'''
import unittest
from io import StringIO
from BuildRulesTable import buildRulesTable
from Utils import LogicRule, PredicateTypes

# What the function returns (Type explanation): 
#   A named tuple. Contents
#     head -> Tuple of two elements the first one is the name, 
#             the second a list with the variables
#     body -> List of tuples. Every tuple contains two elements,
#             the first one the name of the predicate and the
#             second one the list of variables
#     type -> The type of the rules (How many hypothesis it has 1 or 2)
#     lineno -> The line of the rule in the file
#     rule -> string representation of the rule

class TestBuildRulesTable(unittest.TestCase):
    
    def compareRulesTables(self, test_number, good_result, obtained_result):
        def create_temp_error_message(rule, error, obtained, good):
            temp_error_message = " in rule " + str(current_rule) + ":\n"
            temp_error_message += "\tRule: " + rule +\
                        "\tExpected a different " + error +\
                        "\n\tObtained Result: " + str(obtained) + \
                        "\n\tExpected Result: " + str(good)
            return temp_error_message
            
        ErrorMessage = "Error in test " +  str(test_number)
        current_rule = 1
        
        for good, obtained in zip(good_result, obtained_result):
            rule = good.rule
            temp_error_message = create_temp_error_message(rule, 'head', obtained.head, good.head)            
            self.assertTupleEqual(obtained.head, good.head, ErrorMessage + temp_error_message)
            
            temp_error_message = create_temp_error_message(rule, 'body', obtained.body, good.body)            
            self.assertListEqual(obtained.body, good.body, ErrorMessage + temp_error_message)
            
            temp_error_message = create_temp_error_message(rule, 'type', obtained.type, good.type)            
            self.assertEqual(obtained.type, good.type, ErrorMessage + temp_error_message)
            
            temp_error_message = create_temp_error_message(rule, 'line number', obtained.lineno, good.lineno)            
            self.assertEqual(obtained.lineno, good.lineno, ErrorMessage + temp_error_message)
            
            current_rule += 1
            
    def comparePredicateTypes(self, test_number, good_result, obtained_result):
        def create_temp_error_message(error, obtained, good):
            temp_error_message = \
                        "\n\tExpected a different " + error +\
                        "\n\tObtained Result: " + str(obtained) + \
                        "\n\tExpected Result: " + str(good)
            return temp_error_message
            
        ErrorMessage = "Error in test " +  str(test_number)
        
        temp_error_message = create_temp_error_message('intensional set', 
                                                       obtained_result.intensional, 
                                                       good_result.intensional)            
        self.assertSetEqual(obtained_result.intensional, good_result.intensional, 
                              ErrorMessage + temp_error_message)
        
        temp_error_message = create_temp_error_message('extensional set', 
                                                       obtained_result.extensional, 
                                                       good_result.extensional)            
        self.assertSetEqual(obtained_result.extensional, good_result.extensional, 
                              ErrorMessage + temp_error_message)
        
    def compareDependencyGraphs(self, test_number, good_result, obtained_result):
        ErrorMessage = "Error in test " +  str(test_number) +\
                "\n\tExpected a different dependency graph" +\
                "\n\tObtained Result: " + str(obtained_result) + \
                "\n\tExpected Result: " + str(good_result)
                
        self.assertDictEqual(obtained_result, good_result, 
                              ErrorMessage)
        
    def testBuildRulesTable(self):
        FileData = 'TestBuildRuleTableData.txt'
        test_number = 1
        with open(FileData) as f:
            # Read data from file
            # First line is the number test
            while (1):
                f.readline()
                program = ''
                # Next we read the program until we reach the line '# output'
                while (1):
                    line = f.readline()
                    if line[0] == '#': break
                    program += line
                # Read the output
                # rulesTable = eval(f.readline())
                # Rules can be in different lines
                rules = ''
                while (1):
                    rules += f.readline()
                    if rules[-2] == ']': break
                    
                rulesTable = eval(rules)
                predicateTypes = eval(f.readline())
                
                deps = ''
                while(1):
                    deps += f.readline()
                    if deps[-2] == '}': break
                     
                dependencyGraph = eval(deps)
                
                #Check the test
                a,b,c = buildRulesTable(StringIO(unicode(program)), True)
                self.compareRulesTables(test_number, rulesTable, a)
                self.comparePredicateTypes(test_number, predicateTypes, b)
                self.compareDependencyGraphs(test_number, dependencyGraph, c)
                
                test_number += 1
                
                # Read the empty line or the end of file
                c = f.readline()
                if c != '\n': break

        print "Done..."

if __name__ == "__main__":
    #import sys;sys.argv = ['', 'Test.testName']
    unittest.main()