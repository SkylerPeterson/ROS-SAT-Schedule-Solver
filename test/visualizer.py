#!/usr/bin/env python
import matplotlib.pyplot as plt
import networkx as nx

def createGraphVisualization(world, dbData):
    G=nx.Graph()
    
    for edge in world.getGraphEdges():
        G.add_edge(edge[0], edge[1], weight=world.getTravelTime(edge[0], edge[1]))
        G.add_edge(edge[0], edge[0], weight=10)
    
    pathEdges = []
    waitEdges = []
    edgeLabels = dict()
    waitLabels = dict()
    curloc = 'startPos'
    curTask = None
    for task in dbData:
        if task['taskId'].split(':')[0] != 'wait':
            pathEdges.append((curloc, task["location"]))
            edgeLabels[(curloc, task["location"])] = G.edge[curloc][task["location"]]['weight']
            curloc = task["location"]
            curTask = task["taskId"]
        elif task['taskId'].split(':')[0] == 'wait':
            loc = task['taskId'].split(':')[1]
            waitEdges.append((loc, loc))
            waitLabels[(loc, loc)] = world.getTaskTime(curTask)
    
    print waitLabels
    
    pos = nx.circular_layout(G) # positions for all nodes

    # nodes
    nx.draw_networkx_nodes(G, pos, node_size=2500, node_color='blue', node_alpha=0.5)

    # edges
    nx.draw_networkx_edges(G, pos, width=2)
    nx.draw_networkx_edges(G, pos, edgelist=pathEdges, width=4, edge_color='red')
    nx.draw_networkx_edge_labels(G, pos, edge_labels=edgeLabels, label_pos=0.8)
    nx.draw_networkx_edges(G, pos, edgelist=waitEdges, width=4, edge_color='red')
    nx.draw_networkx_edge_labels(G, pos, edge_labels=waitLabels, label_pos=0.5)

    # labels
    nx.draw_networkx_labels(G, pos, font_size=10, font_family='sans-serif')

    plt.axis('off')
    plt.show()


if __name__ == '__main__':
    createGraphVisualization()
