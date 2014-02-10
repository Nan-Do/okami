'''
Created on Jul 26, 2013

@author: nando
'''

from collections import Counter
from copy import deepcopy
from operator import itemgetter
from itertools import groupby
from functools import cmp_to_key

def computeIncidendeGrades(dependencyGraph):
    incidenceGrades = Counter({pred:0 for pred in dependencyGraph.keys()})
    
    for key in dependencyGraph.keys():
        for pred in dependencyGraph[key]:
            incidenceGrades[pred] += 1
        
    return incidenceGrades

def computePredecessors(node, dependencyGraph):
        answer = set([x for x in dependencyGraph[node].keys() if x != node])
        working_set = deepcopy(answer)
        
        while working_set:
            current_node = working_set.pop()
            temp_set = set([x for x in dependencyGraph[current_node].keys() if x not in answer and x != node])
            answer |= temp_set
            working_set |= temp_set
            
        return answer

def orderFirstBlock(block1, block2, predecessors):
#     def computePredecessors(node, dependencyGraph):
#         answer = set([x for x in dependencyGraph[node].keys() if x != node])
#         working_set = deepcopy(answer)
#         
#         while working_set:
#             current_node = working_set.pop()
#             temp_set = set([x for x in dependencyGraph[current_node].keys() if x not in answer and x != node])
#             answer |= temp_set
#             working_set |= temp_set
#             
#         return answer
#         
#     predecessors = dict()
#     for node in block2:
#         predecessors[node] = computePredecessors(node, dependencyGraph)
        
    answer = []
    #print predecessors, block1
    for node in block2:
        for pred in predecessors[node]:
            if pred in block1:
                answer.append(block1)
                
    return answer + list(set(block1).difference(set(answer))) 

def orderSecondBlock(block2, predecessors):
    return sorted(block2, key=cmp_to_key(lambda x, y: 1 if x in predecessors[y] else -1))

def orderThirdBlock(block_1, block_2, block_3, dependencyGraph):
    # Copy the graph 
    graph = deepcopy(dependencyGraph)
    # Remove the nodes of block_1
    for node in block_1:
        del graph[node]
    # Compute the incidence graph in case there is a tie
    iG_1 = computeIncidendeGrades(graph)
    # Remove the nodes of block_2
    for node in block_2:
        del graph[node]
    # Compute the incidence graph to set the order of this block
    iG_2 = computeIncidendeGrades(graph)
    
    sortingBlock = [ (elem, iG_2[elem]) for elem in block_3]
    sortingBlock = sorted(sortingBlock, key=itemgetter(1), reverse=True)
    sortingBlocks = [ list(x[1]) for x in groupby(sortingBlock, key=itemgetter(1)) ] 
    answer = []
    # Check if there is a tie on some nodes of the block and use the previous block to untie
    for block in sortingBlocks:
        if len(block) == 1:
            answer.append(block[0][0])
        else:
            sortingBlock = [ (elem[0], iG_1[elem[0]]) for elem in block]
            sortingBlock = sorted(sortingBlock, key=itemgetter(1), reverse=True)
            answer.extend([x[0] for x in sortingBlock])
    
    return answer
        
def predicateOrder(dependencyGraph, intensionalPredicates):
    block1 = list()
    block2 = list()

    graph = deepcopy(dependencyGraph)
    incidenceGrades = computeIncidendeGrades(graph)
    markedNodes = set()
    addedNodes = [x for x in incidenceGrades.keys() if incidenceGrades[x] == 0]
    
    while (len(addedNodes)):
        markedNodes.update(addedNodes)
        # For every addedNode remove it from the graph
        for node in addedNodes:
            del graph[node]
        
        iG = computeIncidendeGrades(graph)
        addedNodes = [x for x in graph.keys() if iG[x] == 0]
        
    #print markedNodes
    #print incidenceGrades
    for node in markedNodes:
        if incidenceGrades[node] == 0:
            block1.append(node)
        else: block2.append(node)
        
    block3 = list(set(dependencyGraph.keys()).union(intensionalPredicates).difference(markedNodes))
    block3 = orderThirdBlock(block1, block2, block3, dependencyGraph)
    
    predecessors = dict()
    for node in block2:
        predecessors[node] = computePredecessors(node, dependencyGraph)
        
    block2 = orderSecondBlock(block2, predecessors)
    #block1 = orderFirstBlock(block1, block2, dependencyGraph)
    block1 = orderFirstBlock(block1, block2, predecessors)
    
    return (block1, block2, block3)