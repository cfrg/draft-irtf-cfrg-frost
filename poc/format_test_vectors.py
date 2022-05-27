import sys
import json
import textwrap


config_keys = [
    "MAX_SIGNERS",
    "MIN_SIGNERS",
    "NUM_SIGNERS",
]

input_keys = [
    "group_secret_key",
    "group_public_key",
    "message",
]

input_signer_keys = [
    "signer_share",
]

round_one_keys = [
    "participants",
    "group_binding_factor_input",
    "group_binding_factor",
]

round_one_outputs_keys = [
    "hiding_nonce",
    "binding_nonce",
    "hiding_nonce_commitment",
    "binding_nonce_commitment",
]

round_two_keys = [
    "participants",
]

round_two_outputs_keys = [
    "sig_share",
    "group_commitment_share",
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
    for key in input_keys:
        for input_key in vector["inputs"]:
            if key == input_key:
                wrap_print(key + ":", vector["inputs"][key])
    print("")
    print("// Signer input parameters")
    for signer in vector["inputs"]["signers"]:
        for signer_key in input_signer_keys:
            for signer_input_key in vector["inputs"]["signers"][signer]:
                if signer_key == signer_input_key:
                    wrap_print("S" + signer + " " + signer_key + ":", vector["inputs"]["signers"][signer][signer_key])
    print("")

def format_vector_round_one(name, vector):
    print("// Round one parameters")
    for key in round_one_keys:
        for round_one_key in vector["round_one_outputs"]:
            if key == round_one_key:
                wrap_print(key + ":", vector["round_one_outputs"][key])
    print("")
    print("// Signer round one outputs")
    for signer in vector["round_one_outputs"]["signers"]:
        for round_one_signer_key in round_one_outputs_keys:
            for signer_output_key in vector["round_one_outputs"]["signers"][signer]:
                if round_one_signer_key == signer_output_key:
                    wrap_print("S" + signer + " " + round_one_signer_key + ":", vector["round_one_outputs"]["signers"][signer][round_one_signer_key])
    print("")

def format_vector_round_two(name, vector):
    print("// Round two parameters")
    for key in round_two_keys:
        for round_two_key in vector["round_two_outputs"]:
            if key == round_two_key:
                wrap_print(key + ":", vector["round_two_outputs"][key])
    print("")
    print("// Signer round two outputs")
    for signer in vector["round_two_outputs"]["signers"]:
        for round_two_signer_key in round_two_outputs_keys:
            for signer_output_key in vector["round_two_outputs"]["signers"][signer]:
                if round_two_signer_key == signer_output_key:
                    wrap_print("S" + signer + " " + round_two_signer_key + ":", vector["round_two_outputs"]["signers"][signer][round_two_signer_key])
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
