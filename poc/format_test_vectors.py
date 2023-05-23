import sys
import json

config_keys = [
    "MAX_PARTICIPANTS",
    "MIN_PARTICIPANTS",
    "NUM_PARTICIPANTS",
]

input_keys = [
    "group_secret_key",
    "group_public_key",
    "message",
    # "share_polynomial_coefficients" is added manually in format_vector_inputs
]

input_signer_keys = [
    "participant_share",
]

round_one_outputs_keys = [
    "hiding_nonce_randomness",
    "binding_nonce_randomness",
    "hiding_nonce",
    "binding_nonce",
    "hiding_nonce_commitment",
    "binding_nonce_commitment",
    "binding_factor_input",
    "binding_factor",
]

round_two_outputs_keys = [
    "sig_share",
]

final_output_keys = [
    "sig",
]

def wrap_print(arg, *args):
    line_length = 69
    string = arg + " " + " ".join(args)
    for hunk in (string[0+i:line_length+i] for i in range(0, len(string), line_length)):
        if hunk and len(hunk.strip()) > 0:
            print(hunk)

def format_vector_config(name, vector):
    print("// Configuration information")
    for key in config_keys:
        for config_key in vector["config"]:
            if key == config_key:
                wrap_print(key + ":", vector["config"][key])
    print("")

def format_vector_inputs(name, vector):
    print("// Group input parameters")
    print("participant_list: ", end="")
    print(",".join(list(map(lambda i : str(i), vector["inputs"]["participant_list"]))))
    for key in input_keys:
        for input_key in vector["inputs"]:
            if key == input_key:
                wrap_print(key + ":", vector["inputs"][key])

    key = "share_polynomial_coefficients"
    for input_key in vector["inputs"]:
        if key == input_key:
            for i, c in enumerate(vector["inputs"][key]):
                wrap_print(key + "[" + str(i+1) + "]:", c)

    print("")
    print("// Signer input parameters")
    for signer in vector["inputs"]["participant_shares"]:
        for signer_key in input_signer_keys:
            wrap_print("P" + str(signer["identifier"]) + " " + signer_key + ":", signer["participant_share"])
    print("")

def format_vector_round_one(name, vector):
    print("// Signer round one outputs")
    for signer in vector["round_one_outputs"]["outputs"]:
        for round_one_signer_key in round_one_outputs_keys:
            wrap_print("P" + str(signer["identifier"]) + " " + round_one_signer_key + ":", signer[round_one_signer_key])
    print("")

def format_vector_round_two(name, vector):
    print("// Signer round two outputs")
    for signer in vector["round_two_outputs"]["outputs"]:
        for round_two_signer_key in round_two_outputs_keys:
            wrap_print("P" + str(signer["identifier"]) + " " + round_two_signer_key + ":", signer[round_two_signer_key])
    print("")

def format_vector_final_output(name, vector):
    for key in final_output_keys:
        for final_output_key in vector["final_output"]:
            if key == final_output_key:
                wrap_print(key + ":", vector["final_output"][key])

def format_vector(name, vector):
    format_vector_config(name, vector)
    format_vector_inputs(name, vector)
    format_vector_round_one(name, vector)
    format_vector_round_two(name, vector)
    format_vector_final_output(name, vector)

for fname in sys.argv[1:]:
    with open(fname, "r") as fh:
        vector = json.loads(fh.read())
        name = vector["config"]["name"]
        print("")
        print("## " + name + "\n")
        print("~~~")
        format_vector(name, vector)
        print("~~~")
