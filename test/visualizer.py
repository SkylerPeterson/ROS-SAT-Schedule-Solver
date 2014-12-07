#!/usr/bin/env python
import matplotlib.pyplot as plt
import networkx as nx

def createGraphVisualization(world, dbData):
    G=nx.Graph()
    
    for edge in world.getGraphEdges():
        G.add_edge(edge[0], edge[1], weight=world.getTravelTime(edge[0], edge[1]))
    
    pathEdges = []
    curloc = 'startPos'
    for task in dbData:
        pathEdges.append((curloc, task["location"]))
        curloc = task["location"]
    
    pos = nx.circular_layout(G) # positions for all nodes

    # nodes
    nx.draw_networkx_nodes(G, pos, node_size=2500, node_color='blue', node_alpha=0.5)

    # edges
    nx.draw_networkx_edges(G, pos, width=2)
    nx.draw_networkx_edges(G, pos, edgelist=pathEdges, width=4, edge_color='red')

    # labels
    nx.draw_networkx_labels(G, pos, font_size=10, font_family='sans-serif')

    plt.axis('off')
    plt.show()


if __name__ == '__main__':
    createGraphVisualization()
