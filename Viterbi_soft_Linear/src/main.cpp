#include <algorithm>
#include <cassert>
#include <cstdio>
#include <iostream>
#include <limits>
#include <random>
#include <vector>

using namespace std;

template<typename T>
void print_vec(vector<T> const &v) {
    for (int i = 0; i < v.size(); ++i) {
        cout << v[i];
        if (i < v.size() - 1) {
            cout << " ";
        }
    }
    cout << endl;
}

struct Matrix {
    int n;
    int m;

    Matrix(int n, int m): n(n), m(m), data(n, vector<int>(m, 0)) {}

    vector<int>& operator[](int i) {
        return this->data[i];
    }

    friend Matrix minimal_span_form(Matrix const &matrix);
    friend vector<int> encode(vector<int> &x, Matrix const &generator_matrix);
private:
    vector<vector<int>> data;
};

vector<int> vec_xor(vector<int> const &a, vector<int> const &b) {
    assert(a.size() == b.size());

    vector<int> res(a.size(), 0);
    for (int i = 0; i < a.size(); ++i) {
        res[i] = a[i] ^ b[i];
    }
    return res;
}

vector<int> vec_and(vector<int> const &a, vector<int> const &b) {
    assert(a.size() == b.size());

    vector<int> res(a.size(), 0);
    for (int i = 0; i < a.size(); ++i) {
        res[i] = a[i] & b[i];
    }
    return res;
}

vector<int> vec_or(vector<int> const &a, vector<int> const &b) {
    assert(a.size() == b.size());

    vector<int> res(a.size(), 0);
    for (int i = 0; i < a.size(); ++i) {
        res[i] = a[i] | b[i];
    }
    return res;
}

Matrix minimal_span_form(Matrix const &matrix) {
    Matrix res = matrix;

    for (int i = 0, j = 0; i < res.n; ++j) {
        for (int k = i; k < res.n; ++k) {
            if (res.data[k][j] == 1) {
                if (k != i) {
                    res.data[i] = vec_xor(res.data[i], res.data[k]);
                }
                for (int p = i + 1; p < res.n; ++p) {
                    if (res.data[p][j] == 1) {
                        res.data[p] = vec_xor(res.data[p], res.data[i]);
                    }
                }
                ++i;
                break;
            }
        }
    }

    for (int i = res.n - 1; i >= 0; --i) {
        for (int j = res.m - 1; ; --j) {
            if (res.data[i][j] == 1) {
                for (int p = 0; p < i; ++p) {
                    if (res.data[p][j] == 1) {
                        res.data[p] = vec_xor(res.data[p], res.data[i]);
                    }
                }
                break;
            }
        }
    }

    return res;
}

struct Trellis {
    Trellis(Matrix const &matrix) {
        Matrix span_form = minimal_span_form(matrix);

        vector<int> starts(span_form.n, -1);
        for (int i = 0; i < span_form.n; ++i) {
            for (int j = 0; ; ++j) {
                if (span_form[i][j] == 1) {
                    starts[i] = j;
                    break;
                }
            }
        }

        vector<int> ends(span_form.n, -1);
        for (int i = 0; i < span_form.n; ++i) {
            for (int j = span_form.m - 1; ; --j) {
                if (span_form[i][j] == 1) {
                    ends[i] = j;
                    break;
                }
            }
        }

        vector<vector<int>> active_pos_masks = {vector<int>(span_form.n, 0)};
        vector<int> anomaly_pos(1 + span_form.m, -1);
        for (int j = 0; j < span_form.m; ++j) {
            vector<int> active_pos_mask;
            for (int i = 0; i < span_form.n; ++i) {
                if (starts[i] <= j && j < ends[i]) {
                    active_pos_mask.push_back(1);
                } else {
                    active_pos_mask.push_back(0);
                }
                if (starts[i] == j && j == ends[i]) {
                    anomaly_pos[1 + j] = i;
                }
            }
            active_pos_masks.push_back(active_pos_mask);
        }

        vector<vector<Node>> nodes_by_layer = gen_nodes(active_pos_masks);
        int id = 0;
        for (int j = 0; j < nodes_by_layer.size(); ++j) {
            for (Node& v : nodes_by_layer[j]) {
                v.id = id++;
            }
        }

        for (int j = 1; j < nodes_by_layer.size(); ++j) {
            vector<int> col_values(span_form.n, 0);
            for (int i = 0; i < span_form.n; ++i) {
                col_values[i] = span_form[i][j - 1];
            }

            vector<int> active_pos_intersection = vec_and(active_pos_masks[j - 1], active_pos_masks[j]);

            for (Node& u : nodes_by_layer[j - 1]) {
                for (Node& v : nodes_by_layer[j]) {
                    vector<int> u_intersection = vec_and(u.active_pos_values, active_pos_intersection);
                    vector<int> v_intersection = vec_and(v.active_pos_values, active_pos_intersection);

                    if (u_intersection != v_intersection) {
                        continue;
                    }

                    if (anomaly_pos[j] != -1) {
                        v.incoming_edges.push_back(Edge{u.id, 0});
                        v.incoming_edges.push_back(Edge{u.id, 1});
                    } else {
                        vector<int> pos_values = vec_or(u.active_pos_values, v.active_pos_values);
                        pos_values = vec_and(pos_values, col_values);

                        int c = count(pos_values.begin(), pos_values.end(), 1) % 2;
                        v.incoming_edges.push_back(Edge{u.id, c});
                    }
                }
            }
        }

        layers_count = nodes_by_layer.size();
        for (int j = 0; j < nodes_by_layer.size(); ++j) {
            for (Node& v : nodes_by_layer[j]) {
                nodes.push_back(v);
            }
        }
    }

    friend vector<int> decode(Trellis const &trellis, vector<double> &l);
    friend vector<int> get_layers_sizes(Trellis const &trellis);
private:
    struct Edge {
        int initial_id;
        int c;
    };

    struct Node {
        int id;
        int layer;
        vector<int> active_pos_values;
        vector<Edge> incoming_edges;
    };

    int layers_count;
    vector<Node> nodes;

    vector<vector<Node>> gen_nodes(vector<vector<int>> const& active_pos_masks) {
        int code_size = active_pos_masks.size() - 1;
        vector<vector<Node>> res(1 + code_size, vector<Node>());

        for (int layer = 0; layer <= code_size; ++layer) {
            vector<int> active_pos_values;
            gen_nodes_by_mask(layer, active_pos_masks[layer], active_pos_values, res[layer]);
        }

        return res;
    }

    void gen_nodes_by_mask(int layer, vector<int> const& active_pos_mask, vector<int>& active_pos_values, vector<Node>& nodes) {
        if (active_pos_values.size() == active_pos_mask.size()) {
            Node node{-1, layer, active_pos_values, vector<Edge>()};
            nodes.push_back(node);
            return;
        }

        int i = active_pos_values.size();

        active_pos_values.push_back(0);
        gen_nodes_by_mask(layer, active_pos_mask, active_pos_values, nodes);
        active_pos_values.pop_back();

        if (active_pos_mask[i] == 1) {
            active_pos_values.push_back(1);
            gen_nodes_by_mask(layer, active_pos_mask, active_pos_values, nodes);
            active_pos_values.pop_back();
        }
    }
};

vector<int> encode(vector<int> &x, Matrix const &generator_matrix) {
    vector<int> res(generator_matrix.m, 0);
    for (int j = 0; j < generator_matrix.m; ++j) {
        for (int k = 0; k < generator_matrix.n; ++k) {
            res[j] ^= (x[k] & generator_matrix.data[k][j]);
        }
    }
    return res;
}

vector<int> decode(Trellis const &trellis, vector<double> &l) {
    vector<double> weight(trellis.nodes.size(), -numeric_limits<double>::max());
    vector<int> previous_node_id(trellis.nodes.size(), -1);
    vector<int> edge_c(trellis.nodes.size(), -1);
    weight[0] = 0.;

    for (int i = 0; i < trellis.nodes.size(); ++i) {
        for (auto edge : trellis.nodes[i].incoming_edges) {
            double w = edge.c == 0 ? l[trellis.nodes[i].layer - 1] : -l[trellis.nodes[i].layer - 1];
            double new_weight = weight[edge.initial_id] + w;

            if (new_weight > weight[i]) {
                weight[i] = new_weight;
                previous_node_id[i] = edge.initial_id;
                edge_c[i] = edge.c;
            }
        }
    }

    vector<int> res;
    int cur_id = trellis.nodes.size() - 1;
    while (cur_id != 0) {
        res.push_back(edge_c[cur_id]);
        cur_id = previous_node_id[cur_id];
    }

    reverse(res.begin(), res.end());

    return res;
}

double simulate(Matrix const &generator_matrix, Trellis const &trellis,
                double noise_level, int num_of_iterations, int max_errors) {
    int inf_size = generator_matrix.n;
    int code_size = generator_matrix.m;
    double sigma = sqrt(0.5 *
                        pow(10., - noise_level / 10.) *
                        (double) code_size / (double) inf_size
                       );

    mt19937 gen32;
    normal_distribution<double> d{0, sigma};

    int it, errors;
    for (it = 0, errors = 0; it < num_of_iterations && errors < max_errors; ++it) {
        vector<int> inf_vec(inf_size, 0);
        for (int i = 0; i < inf_size; ++i) {
            inf_vec[i] = gen32() & 1;
        }

        vector<int> code_vec = encode(inf_vec, generator_matrix);

        vector<double> signal_vec(code_size, 0.);
        for (int i = 0; i < code_size; ++i) {
            signal_vec[i] = (2. * code_vec[i] - 1.) + d(gen32);
        }

        vector<double> l(code_size, 0.);
        for (int i = 0; i < code_size; ++i) {
            l[i] = -2. * signal_vec[i] / (sigma * sigma);
        }

        vector<int> decoded_vec = decode(trellis, l);
        if (code_vec != decoded_vec) {
            ++errors;
        }
    }

    return (double) errors / it;
}

vector<int> get_layers_sizes(Trellis const &trellis) {
    vector<int> res(trellis.layers_count, 0);
    for (int i = 0; i < trellis.nodes.size(); ++i) {
        ++res[trellis.nodes[i].layer];
    }
    return res;
}

int main() {
    if (!freopen("input.txt", "r", stdin)) {
        return 1;
    }
    if (!freopen("output.txt", "w", stdout)) {
        return 2;
    }

    int n, k;
    cin >> n >> k;

    Matrix generator_matrix = Matrix(k, n);
    for (int i = 0; i < k; ++i) {
        for (int j = 0; j < n; ++j) {
            cin >> generator_matrix[i][j];
        }
    }

    Trellis trellis = Trellis(generator_matrix);
    print_vec(get_layers_sizes(trellis));

    string command;
    while (cin >> command) {
        if (command == "Encode") {
            vector<int> inf_vec(k, 0);
            for (int i = 0; i < k; ++i) {
                cin >> inf_vec[i];
            }
            print_vec(encode(inf_vec, generator_matrix));
        } else if (command == "Decode") {
            vector<double> l(n, 0.);
            for (int i = 0; i < n; ++i) {
                cin >> l[i];
            }
            print_vec(decode(trellis, l));
        } else if (command == "Simulate") {
            double noise_level;
            int num_of_iterations;
            int max_errors;
            cin >> noise_level >> num_of_iterations >> max_errors;
            cout << simulate(generator_matrix, trellis, noise_level, num_of_iterations, max_errors) << endl;
        }
    }

    return 0;
}