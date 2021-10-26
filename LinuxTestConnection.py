#!/usr/bin/env python
from __future__ import print_function
import os
import re
import sys
import json
import shlex
import subprocess

import datetime
import platform
if os.name != "nt": import pwd  # do not make this multi-line - the packager won't package correctly
import time
import uuid
from abc import ABCMeta, abstractmethod
import os.path
import socket
import imp
import codecs
import string
if sys.version_info[0] == 2:
    from urlparse import urlparse
else:
    from urllib.parse import urlparse
from os import walk

_UNIXCONFDIR = os.environ.get('UNIXCONFDIR', '/etc')
_OS_RELEASE_BASENAME = 'os-release'

NORMALIZED_OS_ID = {
    'ol': 'oracle',  # Oracle Linux
}

NORMALIZED_LSB_ID = {
    'enterpriseenterpriseas': 'oracle',  # Oracle Enterprise Linux 4
    'enterpriseenterpriseserver': 'oracle',  # Oracle Linux 5
    'redhatenterpriseworkstation': 'rhel',  # RHEL 6, 7 Workstation
    'redhatenterpriseserver': 'rhel',  # RHEL 6, 7 Server
    'redhatenterprisecomputenode': 'rhel',  # RHEL 6 ComputeNode
}

NORMALIZED_DISTRO_ID = {
    'redhat': 'rhel',  # RHEL 6.x, 7.x
}

# Pattern for content of distro release file (reversed)
_DISTRO_RELEASE_CONTENT_REVERSED_PATTERN = re.compile(
    r'(?:[^)]*\)(.*)\()? *(?:STL )?([\d.+\-a-z]*\d) *(?:esaeler *)?(.+)')

# Pattern for base file name of distro release file
_DISTRO_RELEASE_BASENAME_PATTERN = re.compile(
    r'(\w+)[-_](release|version)$')

# Base file names to be ignored when searching for distro release file
_DISTRO_RELEASE_IGNORE_BASENAMES = (
    'debian_version',
    'lsb-release',
    'oem-release',
    _OS_RELEASE_BASENAME,
    'system-release',
    'plesk-release',
)

oms_admin_conf_path = "/etc/opt/microsoft/omsagent/conf/omsadmin.conf"
# oms_agent_dir = "/var/opt/microsoft/omsagent"
# oms_agent_log = "/var/opt/microsoft/omsagent/log/omsagent.log"
# current_mof = "/etc/opt/omi/conf/omsconfig/configuration/Current.mof"
status_passed = "Passed"
status_failed = "Failed"
status_debug = "Debug"
empty_failure_reason = ""
workspace = ""
automation = ""

rule_info_list = []
output = []

class cached_property(object):
    def __init__(self, f):
        self._fname = f.__name__
        self._f = f

    def __get__(self, obj, owner):
        assert obj is not None, 'call {} on an instance'.format(self._fname)
        ret = obj.__dict__[self._fname] = self._f(obj)
        return ret

#distro https://distro.readthedocs.io/en/latest/#linuxdistribution-class
class LinuxDistribution(object):
    def __init__(self,
                 include_lsb=True,
                 os_release_file='',
                 distro_release_file='',
                 include_uname=True):
        self.os_release_file = os_release_file or \
            os.path.join(_UNIXCONFDIR, _OS_RELEASE_BASENAME)
        self.distro_release_file = distro_release_file or ''  # updated later
        self.include_lsb = include_lsb
        self.include_uname = include_uname

    def __repr__(self):
        """Return repr of all info
        """
        return \
            "LinuxDistribution(" \
            "os_release_file={self.os_release_file!r}, " \
            "distro_release_file={self.distro_release_file!r}, " \
            "include_lsb={self.include_lsb!r}, " \
            "include_uname={self.include_uname!r}, " \
            "_os_release_info={self._os_release_info!r}, " \
            "_lsb_release_info={self._lsb_release_info!r}, " \
            "_distro_release_info={self._distro_release_info!r}, " \
            "_uname_info={self._uname_info!r})".format(
                self=self)

    def linux_distribution(self, full_distribution_name=True):
        return (
            self.name() if full_distribution_name else self.id(),
            self.version(),
            self.codename()
        )

    def id(self):
        def normalize(distro_id, table):
            distro_id = distro_id.lower().replace(' ', '_')
            return table.get(distro_id, distro_id)

        distro_id = self.os_release_attr('id')
        if distro_id:
            return normalize(distro_id, NORMALIZED_OS_ID)

        distro_id = self.lsb_release_attr('distributor_id')
        if distro_id:
            return normalize(distro_id, NORMALIZED_LSB_ID)

        distro_id = self.distro_release_attr('id')
        if distro_id:
            return normalize(distro_id, NORMALIZED_DISTRO_ID)

        distro_id = self.uname_attr('id')
        if distro_id:
            return normalize(distro_id, NORMALIZED_DISTRO_ID)

        return ''

    def name(self, pretty=False):
        name = self.os_release_attr('name') \
            or self.lsb_release_attr('distributor_id') \
            or self.distro_release_attr('name') \
            or self.uname_attr('name')
        if pretty:
            name = self.os_release_attr('pretty_name') \
                or self.lsb_release_attr('description')
            if not name:
                name = self.distro_release_attr('name') \
                       or self.uname_attr('name')
                version = self.version(pretty=True)
                if version:
                    name = name + ' ' + version
        return name or ''

    def version(self, pretty=False, best=False):
        versions = [
            self.os_release_attr('version_id'),
            self.lsb_release_attr('release'),
            self.distro_release_attr('version_id'),
            self._parse_distro_release_content(
                self.os_release_attr('pretty_name')).get('version_id', ''),
            self._parse_distro_release_content(
                self.lsb_release_attr('description')).get('version_id', ''),
            self.uname_attr('release')
        ]
        version = ''
        if best:
            for v in versions:
                if v.count(".") > version.count(".") or version == '':
                    version = v
        else:
            for v in versions:
                if v != '':
                    version = v
                    break
        if pretty and version and self.codename():
            version = '{0} ({1})'.format(version, self.codename())
        return version

    def version_parts(self, best=False):
        version_str = self.version(best=best)
        if version_str:
            version_regex = re.compile(r'(\d+)\.?(\d+)?\.?(\d+)?')
            matches = version_regex.match(version_str)
            if matches:
                major, minor, build_number = matches.groups()
                return major, minor or '', build_number or ''
        return '', '', ''

    def major_version(self, best=False):
        return self.version_parts(best)[0]

    def minor_version(self, best=False):
        return self.version_parts(best)[1]

    def build_number(self, best=False):
        return self.version_parts(best)[2]

    def like(self):
        return self.os_release_attr('id_like') or ''

    def codename(self):
        try:
            # this to empty string to have no codename
            return self._os_release_info['codename']
        except KeyError:
            return self.lsb_release_attr('codename') \
                or self.distro_release_attr('codename') \
                or ''

    def info(self, pretty=False, best=False):
        return dict(
            id=self.id(),
            version=self.version(pretty, best),
            version_parts=dict(
                major=self.major_version(best),
                minor=self.minor_version(best),
                build_number=self.build_number(best)
            ),
            like=self.like(),
            codename=self.codename(),
        )

    def os_release_info(self):
        return self._os_release_info

    def lsb_release_info(self):
        return self._lsb_release_info

    def distro_release_info(self):
        return self._distro_release_info

    def uname_info(self):
        return self._uname_info

    def os_release_attr(self, attribute):
        return self._os_release_info.get(attribute, '')

    def lsb_release_attr(self, attribute):
        return self._lsb_release_info.get(attribute, '')

    def distro_release_attr(self, attribute):
        return self._distro_release_info.get(attribute, '')

    def uname_attr(self, attribute):
        return self._uname_info.get(attribute, '')

    @cached_property
    def _os_release_info(self):
        if os.path.isfile(self.os_release_file):
            with open(self.os_release_file) as release_file:
                return self._parse_os_release_content(release_file)
        return {}

    @staticmethod
    def _parse_os_release_content(lines):
        props = {}
        lexer = shlex.shlex(lines, posix=True)
        lexer.whitespace_split = True

        if sys.version_info[0] == 2 and isinstance(lexer.wordchars, bytes):
            lexer.wordchars = lexer.wordchars.decode('iso-8859-1')

        tokens = list(lexer)
        for token in tokens:
            if '=' in token:
                k, v = token.split('=', 1)
                props[k.lower()] = v
            else:
                # Ignore any tokens that are not variable assignments
                pass

        if 'version_codename' in props:
            # os-release added a version_codename field.  Use that in
            # preference to anything else Note that some distros purposefully
            # do not have code names.  They should be setting
            # version_codename=""
            props['codename'] = props['version_codename']
        elif 'ubuntu_codename' in props:
            # Same as above but a non-standard field name used on older Ubuntus
            props['codename'] = props['ubuntu_codename']
        elif 'version' in props:
            # If there is no version_codename, parse it from the version
            codename = re.search(r'(\(\D+\))|,(\s+)?\D+', props['version'])
            if codename:
                codename = codename.group()
                codename = codename.strip('()')
                codename = codename.strip(',')
                codename = codename.strip()
                # codename appears within paranthese.
                props['codename'] = codename

        return props

    @cached_property
    def _lsb_release_info(self):
        if not self.include_lsb:
            return {}
        with open(os.devnull, 'w') as devnull:
            try:
                cmd = ('lsb_release', '-a')
                stdout = subprocess.check_output(cmd, stderr=devnull)
            except OSError:  # Command not found
                return {}
        content = self._to_str(stdout).splitlines()
        return self._parse_lsb_release_content(content)

    @staticmethod
    def _parse_lsb_release_content(lines):
        props = {}
        for line in lines:
            kv = line.strip('\n').split(':', 1)
            if len(kv) != 2:
                # Ignore lines without colon.
                continue
            k, v = kv
            props.update({k.replace(' ', '_').lower(): v.strip()})
        return props

    @cached_property
    def _uname_info(self):
        with open(os.devnull, 'w') as devnull:
            try:
                cmd = ('uname', '-rs')
                stdout = subprocess.check_output(cmd, stderr=devnull)
            except OSError:
                return {}
        content = self._to_str(stdout).splitlines()
        return self._parse_uname_content(content)

    @staticmethod
    def _parse_uname_content(lines):
        props = {}
        match = re.search(r'^([^\s]+)\s+([\d\.]+)', lines[0].strip())
        if match:
            name, version = match.groups()

            if name == 'Linux':
                return {}
            props['id'] = name.lower()
            props['name'] = name
            props['release'] = version
        return props

    @staticmethod
    def _to_str(text):
        encoding = sys.getfilesystemencoding()
        encoding = 'utf-8' if encoding == 'ascii' else encoding

        if sys.version_info[0] >= 3:
            if isinstance(text, bytes):
                return text.decode(encoding)
        else:
            if isinstance(text, unicode):  # noqa
                return text.encode(encoding)

        return text

    @cached_property
    def _distro_release_info(self):
        if self.distro_release_file:
            # If it was specified, we use it and parse what we can, even if
            # its file name or content does not match the expected pattern.
            distro_info = self._parse_distro_release_file(
                self.distro_release_file)
            basename = os.path.basename(self.distro_release_file)
            # The file name pattern for user-specified distro release files
            # is somewhat more tolerant (compared to when searching for the
            # file), because we want to use what was specified as best as
            # possible.
            match = _DISTRO_RELEASE_BASENAME_PATTERN.match(basename)
            if 'name' in distro_info \
               and 'cloudlinux' in distro_info['name'].lower():
                distro_info['id'] = 'cloudlinux'
            elif match:
                distro_info['id'] = match.group(1)
            return distro_info
        else:
            try:
                basenames = os.listdir(_UNIXCONFDIR)
                basenames.sort()
            except OSError:
                basenames = ['SuSE-release',
                             'arch-release',
                             'base-release',
                             'centos-release',
                             'fedora-release',
                             'gentoo-release',
                             'mageia-release',
                             'mandrake-release',
                             'mandriva-release',
                             'mandrivalinux-release',
                             'manjaro-release',
                             'oracle-release',
                             'redhat-release',
                             'sl-release',
                             'slackware-version']
            for basename in basenames:
                if basename in _DISTRO_RELEASE_IGNORE_BASENAMES:
                    continue
                match = _DISTRO_RELEASE_BASENAME_PATTERN.match(basename)
                if match:
                    filepath = os.path.join(_UNIXCONFDIR, basename)
                    distro_info = self._parse_distro_release_file(filepath)
                    if 'name' in distro_info:
                        # The name is always present if the pattern matches
                        self.distro_release_file = filepath
                        distro_info['id'] = match.group(1)
                        if 'cloudlinux' in distro_info['name'].lower():
                            distro_info['id'] = 'cloudlinux'
                        return distro_info
            return {}

    def _parse_distro_release_file(self, filepath):
        """
        Parse a distro release file.
        Parameters:
        * filepath: Path name of the distro release file.
        Returns:
            A dictionary containing all information items.
        """
        try:
            with open(filepath) as fp:
                return self._parse_distro_release_content(fp.readline())
        except (OSError, IOError):
            return {}

    @staticmethod
    def _parse_distro_release_content(line):
        matches = _DISTRO_RELEASE_CONTENT_REVERSED_PATTERN.match(
            line.strip()[::-1])
        distro_info = {}
        if matches:
            # regexp ensures non-None
            distro_info['name'] = matches.group(3)[::-1]
            if matches.group(2):
                distro_info['version_id'] = matches.group(2)[::-1]
            if matches.group(1):
                distro_info['codename'] = matches.group(1)[::-1]
        elif line:
            distro_info['name'] = line.strip()
        return distro_info

#python self Utility class, need check further
class Utility(object):
    """Utility class has utility functions used by other modules"""
    LINUX_DISTRO = LinuxDistribution()

    def __init__(self):
        self.standard_datetime_format = "%Y-%m-%dT%H:%M:%S"
        self.touch_cmd = 'sudo touch '
        self.chown_cmd = 'sudo chown '
        self.omsagentusergroup = 'omsagent:omiusers '
        self.chmod_cmd = 'sudo chmod '
        self.permissions = 'u=rw,g=rw,o=r '

    def run_command_output(self, cmd, no_output, chk_err=True):
        def check_output(no_output, *popenargs, **kwargs):
            """
            Backport from subprocess module from python 2.7
            """
            if 'stdout' in kwargs:
                raise ValueError(
                    'stdout argument not allowed, it will be overridden.')
            if no_output is True:
                out_file = None
            else:
                out_file = subprocess.PIPE

            process = subprocess.Popen(stdout=out_file, *popenargs, **kwargs)
            output, unused_err = process.communicate()
            retcode = process.poll()

            if retcode:
                cmd = kwargs.get("args")
                if cmd is None:
                    cmd = popenargs[0]
                raise subprocess.CalledProcessError(retcode,
                                                    cmd, output=output)
            return output

        class CalledProcessError(Exception):
            """Exception classes used by this module."""

            def __init__(self, returncode, cmd, output=None):
                self.returncode = returncode
                self.cmd = cmd
                self.output = output

            def __str__(self):
                return "Command '%s' returned non-zero exit status %d" \
                       % (self.cmd, self.returncode)

        subprocess.check_output = check_output
        subprocess.CalledProcessError = CalledProcessError
        try:
            output = subprocess.check_output(
                no_output, cmd, stderr=subprocess.STDOUT, shell=True)
        except subprocess.CalledProcessError as e:
            if chk_err:
                print("Error: CalledProcessError.  Error Code is: " + str(e.returncode), file=sys.stdout)
                print("Error: CalledProcessError.  Command string was: " + e.cmd, file=sys.stdout)
                print("Error: CalledProcessError.  Command result was: " +
                      self.get_subprocess_output_as_asciistring((e.output[:-1])), file=sys.stdout)
            if no_output:
                return e.returncode, None
            else:
                return e.returncode, self.get_subprocess_output_as_asciistring(e.output)

        if no_output:
            return 0, None
        else:
           return 0, self.get_subprocess_output_as_asciistring(output)
    

    def get_subprocess_output_as_asciistring(self, subprocess_output):
        if subprocess_output is None:
            return None
        
        # python 3
        if sys.version_info[0] >= 3:
            return subprocess_output.decode('ascii', 'ignore')

        return subprocess_output.decode('utf8', 'ignore').encode('ascii', 'ignore')
    
    @staticmethod
    def get_linux_distribution():
        return Utility.LINUX_DISTRO.linux_distribution(full_distribution_name=False)  

utils = Utility()

def find_line_in_file(search_text, path, file_encoding=""):
    if os.path.isfile(path):
        if file_encoding == "":
            current_file = open(path, "r")
        else:
            current_file = codecs.open(path, "r", file_encoding)

        for line in current_file:
            if search_text in line:
                current_file.close()
                return line

        current_file.close()
    return None

def get_workspace():
    line = find_line_in_file("WORKSPACE", oms_admin_conf_path)
    if line is not None:
        return line.split("=")[1].strip()

    return None

def get_machine_info():
    FNULL = open(os.devnull, "w")
    if subprocess.call(["which", "hostnamectl"], stdout=FNULL, stderr=FNULL) == 0:
        hostname_output = os.popen("hostnamectl").read()
        write_log_output(None, None, status_debug, empty_failure_reason, "Machine Information:" + hostname_output)
    FNULL.close()
    return hostname_output

class RuleInfo:
    def __init__(self, rule_id, rule_group_id, status, result_msg_id):
        self.RuleId = rule_id
        self.RuleGroupId = rule_group_id
        self.CheckResult = status
        self.CheckResultMessageId = result_msg_id
        self.CheckResultMessageArguments = list()

def write_log_output(rule_id, rule_group_id, status, failure_reason, log_msg, *result_msg_args):
    global output, rule_info_list

    if(type(log_msg) != str):
        log_msg = str(log_msg)

    if status != status_debug:
        if failure_reason == empty_failure_reason:
            result_msg_id = rule_id + "." + status
        else:
            result_msg_id = rule_id + "." + status + "." + failure_reason

        current_rule_info = RuleInfo(rule_id, rule_group_id, status, result_msg_id)
        #ask pointers and display message in recursion
        result_msg_args_list = []
        for arg in result_msg_args:
            current_rule_info.CheckResultMessageArguments.append(arg)

        rule_info_list.append(current_rule_info)

    output.append(status + ": " + log_msg + "\n")

def check_os_version():
    rule_id = "LinuxOS.MMA"
    rule_group_id = "prerequisites"
    os_tuple = utils.get_linux_distribution()
    os_version = os_tuple[0] + "-" + os_tuple[1]
    supported_os_url = "https://docs.microsoft.com/en-us/azure/azure-monitor/agents/agents-overview#linux"
    # list all support OS for MMA
    if re.search("Ubuntu-14.04", os_version, re.IGNORECASE) or \
       re.search("Ubuntu-16.04", os_version, re.IGNORECASE) or \
       re.search("Ubuntu-18.04", os_version, re.IGNORECASE) or \
       re.search("Ubuntu-20.04", os_version, re.IGNORECASE) or \
       re.search("SuSE-12", os_version, re.IGNORECASE) or \
       re.search("SLES-12", os_version, re.IGNORECASE) or \
       re.search("SLES-15", os_version, re.IGNORECASE) or \
       re.search("SuSE-15", os_version, re.IGNORECASE) or \
       re.search("rhel-6", os_version, re.IGNORECASE) or \
       re.search("rhel-7", os_version, re.IGNORECASE) or \
       re.search("rhel-8", os_version, re.IGNORECASE) or \
       re.search("centos-6", os_version, re.IGNORECASE) or \
       re.search("centos-8", os_version, re.IGNORECASE) or \
       re.search("centos-7", os_version, re.IGNORECASE) or \
       re.search("Oracle-6", os_version, re.IGNORECASE) or \
       re.search("Oracle-8", os_version, re.IGNORECASE) or \
       re.search("Oracle-7", os_version, re.IGNORECASE) :
        write_log_output(rule_id, rule_group_id, status_passed, empty_failure_reason, "Operating system version is supported")
    else:
        log_msg = "Operating System version (%s) is not supported. Supported versions listed here: %s" % (os_version, supported_os_url)
        write_log_output(rule_id, rule_group_id, status_failed, empty_failure_reason, log_msg, supported_os_url)

def check_proxy_connectivity():
    rule_id = "Linux.ProxyCheck"
    rule_group_id = "connectivity"

    if os.environ.get('HTTP_PROXY') is None and \
       os.environ.get('HTTPS_PROXY') is None and \
       os.environ.get('http_proxy') is None and \
       os.environ.get('https_proxy') is None:
        write_log_output(rule_id, rule_group_id, status_passed, empty_failure_reason, "Machine has no proxy enabled.")
    else:
        write_log_output(rule_id, rule_group_id, status_failed, empty_failure_reason, "Machine has proxy enabled, please check your proxy configuration if any connection failure.")

def check_imds_connectivity():
    rule_id = "Linux.ImdsCheck"
    rule_group_id = "connectivity"

    write_log_output(None, None, status_debug, empty_failure_reason, "Log analytics connection test.")
    curl_cmd = "curl -H Metadata:true --noproxy \"*\" \"http://169.254.169.254/metadata/instance?api-version=2021-02-01\""
    code, out = utils.run_command_output(curl_cmd, False, False)

    if code == 0:
        #write_log_output(rule_id, rule_group_id, status_debug, empty_failure_reason, "IMDS Server Information: " + str(out))
        write_log_output(rule_id, rule_group_id, status_passed, empty_failure_reason, "Machine is able to reach IMDS server.")
    else:
        write_log_output(rule_id, rule_group_id, status_failed, empty_failure_reason, "Machine is not able to reach IMDS server. Applicable to azure machines only. See debugging guidelines: https://docs.microsoft.com/en-us/azure/virtual-machines/windows/instance-metadata-service?tabs=linux#errors-and-debugging")

def is_fairfax_region():
    oms_endpoint = find_line_in_file("OMS_ENDPOINT", oms_admin_conf_path)
    if oms_endpoint is not None:
        return ".us" in oms_endpoint.split("=")[1]

def check_endpoint(workspace, endpoint):
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    new_endpoint = None
    sock.settimeout(180) #180s
    if "*" in endpoint and workspace is not None:
        new_endpoint = endpoint.replace("*", workspace)
    elif "*" not in endpoint:
        new_endpoint = endpoint

    if new_endpoint is not None:
        try:
            response = sock.connect_ex((new_endpoint, 443))

            if response == 0:
                return True
            else:
                return False

        except Exception as ex:
            return False
    else:
        return False

def check_log_analytics_endpoints():
    rule_id = "Linux.LogAnalyticsConnectivityCheck"
    rule_group_id = "connectivity"

    i = 0
    #if it's fairefax, endpoint ends by *.opinsights.azure.us https://docs.microsoft.com/en-us/azure/azure-government/compare-azure-government-global-azure#networking
    if is_fairfax_region() is True:
        fairfax_log_analytics_endpoints = ["usge-jobruntimedata-prod-1.usgovtrafficmanager.net", "usge-agentservice-prod-1.usgovtrafficmanager.net",
                    "*.ods.opinsights.azure.us", "*.oms.opinsights.azure.us" ]

        for endpoint in fairfax_log_analytics_endpoints:
            i += 1
            if "*" in endpoint and workspace is not None:
                endpoint = endpoint.replace("*", workspace)
 
            if check_endpoint(workspace, endpoint):
                write_log_output(rule_id + str(i), rule_group_id, status_passed, empty_failure_reason, "TCP test for {" + endpoint + "} (port 443) succeeded", endpoint)
            else:
                write_log_output(rule_id + str(i), rule_group_id, status_failed, empty_failure_reason, "TCP test for {" + endpoint + "} (port 443) failed", endpoint)
            
            check_ssl_connectivity(endpoint)
    else:
        log_analytics_endpoints = ["*.ods.opinsights.azure.com", "*.oms.opinsights.azure.com", "ods.systemcenteradvisor.com", "scadvisorcontent.blob.core.windows.net"]
        for endpoint in log_analytics_endpoints:
            i += 1
            if "*" in endpoint and workspace is not None:
                endpoint = endpoint.replace("*", workspace)

            if check_endpoint(workspace, endpoint):
                write_log_output(rule_id + str(i), rule_group_id, status_passed, empty_failure_reason, "TCP test for {" + endpoint + "} (port 443) succeeded", endpoint)
            else:
                write_log_output(rule_id + str(i), rule_group_id, status_failed, empty_failure_reason, "TCP test for {" + endpoint + "} (port 443) failed, please check your network and firewall configuration https://docs.microsoft.com/en-us/azure/azure-monitor/agents/log-analytics-agent#firewall-requirements; if private link enabled, please add .privatelink. to verify the connection https://docs.microsoft.com/en-us/azure/azure-monitor/logs/private-link-configure#review-and-validate-your-private-link-setup, for example <workspace id>.privatelink.oms.opinsights.azure.com:443", endpoint)
            
            check_ssl_connectivity(endpoint)

def check_full_endpoint(endpoint):
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.settimeout(180) #180s

    if endpoint is not None:
        try:
            response = sock.connect_ex((endpoint, 443))

            if response == 0:
                return True
            else:
                return False

        except Exception as ex:
            return False
    else:
        return False

def check_lad_endpoints(sa=None, eh=None):
    rule_id = "Linux.LADConnectivityCheck"
    rule_group_id = "connectivity"

    # lad_endpoints = ["*.table.core.windows.net", "*.servicebus.windows.net"]
    new_endpoint = None
    #endpoints = []
    if sa is not None:
        new_endpoint = "%s.table.core.windows.net" % (sa)
        # print(lad_endpoints[0])
        if check_full_endpoint(new_endpoint):
            write_log_output(rule_id, rule_group_id, status_passed, empty_failure_reason, "TCP test for {" + new_endpoint + "} (port 443) succeeded", new_endpoint)
        else:
            write_log_output(rule_id, rule_group_id, status_failed, empty_failure_reason, "TCP test for {" + new_endpoint + "} (port 443) failed", new_endpoint)
        
        check_ssl_connectivity(new_endpoint)

    if eh is not None:
        new_endpoint = "%s.servicebus.windows.net" % (eh)
        if check_full_endpoint(new_endpoint):
            write_log_output(rule_id, rule_group_id, status_passed, empty_failure_reason, "TCP test for {" + new_endpoint + "} (port 443) succeeded", new_endpoint)
        else:
            write_log_output(rule_id, rule_group_id, status_failed, empty_failure_reason, "TCP test for {" + new_endpoint + "} (port 443) failed", new_endpoint)
        
        check_ssl_connectivity(new_endpoint)
    # for endpoint in lad_endpoints:
    #     i += 1
    #     if check_full_endpoint(endpoint):
    #         write_log_output(rule_id + str(i), rule_group_id, status_passed, empty_failure_reason, "TCP123 test for {" + endpoint + "} (port 443) succeeded", endpoint)
    #     else:
    #         write_log_output(rule_id + str(i), rule_group_id, status_failed, empty_failure_reason, "TCP123 test for {" + endpoint + "} (port 443) failed", endpoint)

def check_ssl_connectivity(endpoint):
    rule_id = "Linux.SSLCheck"
    rule_group_id = "connectivity"
    FNULL = open(os.devnull, "w")
    if endpoint is not None and subprocess.call(["which", "openssl"], stdout=FNULL, stderr=FNULL) == 0:
        openssl_cmd = "echo \"q\" | openssl s_client -connect %s:443" % (endpoint)
        code, out = utils.run_command_output(openssl_cmd, False, False)       
        if code == 0 and "CONNECTED" in out:
            write_log_output(rule_id, rule_group_id, status_passed, empty_failure_reason, "SSL test for {" + endpoint + "} (port 443) succeeded")
        else:
            write_log_output(rule_id, rule_group_id, status_failed, empty_failure_reason, "SSL test for {" + endpoint + "} (port 443) failed")
    
    FNULL.close()

def check_lad_ssl_connectivity(sa=None, eh=None):
    rule_id = "Linux.LADSSLCheck"
    rule_group_id = "connectivity"
    FNULL = open(os.devnull, "w")
    if sa is not None and subprocess.call(["which", "openssl"], stdout=FNULL, stderr=FNULL) == 0:
        openssl_sa = "echo \"q\" | openssl s_client -connect %s.table.core.windows.net:443" % (sa)
        code, out = utils.run_command_output(openssl_sa, False, False)       
        if code == 0 and "CONNECTED" in out:
            write_log_output(rule_id, rule_group_id, status_passed, empty_failure_reason, "SSL test for {" + sa + ".table.core.windows.net} (port 443) succeeded")
        else:
            write_log_output(rule_id, rule_group_id, status_failed, empty_failure_reason, "SSL test for {" + sa + ".table.core.windows.net} (port 443) failed")
    
    if eh is not None and subprocess.call(["which", "openssl"], stdout=FNULL, stderr=FNULL) == 0:
        openssl_eh = "echo \"q\" | openssl s_client -connect %s.servicebus.windows.net:443" % (eh)
        code, out = utils.run_command_output(openssl_eh, False, False)       
        if code == 0 and "CONNECTED" in out:
            write_log_output(rule_id, rule_group_id, status_passed, empty_failure_reason, "SSL test for {" + eh + ".table.core.windows.net} (port 443) succeeded")
        else:
            write_log_output(rule_id, rule_group_id, status_failed, empty_failure_reason, "SSL test for {" + eh + ".table.core.windows.net} (port 443) failed")
    
    FNULL.close()

def get_automation(workspace):
    if workspace is not None:
        worker_conf_path = "/var/opt/microsoft/omsagent/%s/state/automationworker/worker.conf" % (workspace)
        line = find_line_in_file("account_id", worker_conf_path)
        if line is not None:
            return line.split("=")[1].strip()

def get_agent_endpoint():
    line = find_line_in_file("agentsvc", oms_admin_conf_path)
    # Fetch the text after https://
    if line is not None:
        return line.split("=")[1].split("/")[2].strip()

    return None

def check_dsc_agent_endpoint():
    rule_id = "Linux.AutomationServiceConnectivityCheck"
    rule_group_id = "connectivity"

    agent_endpoint = get_agent_endpoint()
    if  agent_endpoint is None:
        write_log_output(rule_id, rule_group_id, status_failed, "UnableToGetEndpoint", "Unable to get the registration (agent service) endpoint")
    elif  check_endpoint(None, agent_endpoint):
        write_log_output(rule_id, rule_group_id, status_passed, empty_failure_reason, "TCP test for {" + agent_endpoint + "} (port 443) succeeded", agent_endpoint)
    else:
        write_log_output(rule_id, rule_group_id, status_failed, empty_failure_reason, "TCP test for {" + agent_endpoint + "} (port 443) failed, please check if DSC modules are downloaded correctly under /opt/microsoft/omsconfig/module_packages, if not, please check .mof files under /etc/opt/omi/conf/omsconfig/configuration/. Once network issue fixed, please purge and re-enable agent https://docs.microsoft.com/en-us/azure/azure-monitor/agents/agent-linux-troubleshoot#purge-and-re-install-the-linux-agent", agent_endpoint)
    
    if agent_endpoint is not None:
        check_ssl_connectivity(agent_endpoint)

def get_jrds_endpoint(workspace):
    if workspace is not None:
        worker_conf_path = "/var/opt/microsoft/omsagent/%s/state/automationworker/worker.conf" % (workspace)
        line = find_line_in_file("jrds_base_uri", worker_conf_path)
        if line is not None:
            return line.split("=")[1].split("/")[2].strip()

def get_aa_region(workspace):
    if workspace is not None:
        worker_conf_path = "/var/opt/microsoft/omsagent/%s/state/automationworker/worker.conf" % (workspace)
        line = find_line_in_file("jrds_base_uri", worker_conf_path)
        if line is not None:
            return line.split("=")[1].split("/")[2].split("-")[0].strip()

def check_jrds_endpoint(workspace):
    rule_id = "Linux.JRDSConnectivityCheck"
    rule_group_id = "connectivity"

    jrds_endpoint = get_jrds_endpoint(workspace)
    if jrds_endpoint is None:
        write_log_output(rule_id, rule_group_id, status_failed, "UnableToGetEndpoint", "Unable to get the operations (JRDS) endpoint")
    elif jrds_endpoint is not None and check_endpoint(workspace, jrds_endpoint):
        write_log_output(rule_id, rule_group_id, status_passed, empty_failure_reason, "TCP test for {" + jrds_endpoint + "} (port 443) succeeded", jrds_endpoint)
    else:
        write_log_output(rule_id, rule_group_id, status_failed, empty_failure_reason, "TCP test for {" + jrds_endpoint + "} (port 443) failed, please allow it for automation solution https://docs.microsoft.com/en-us/azure/automation/how-to/automation-region-dns-records#dns-records-per-region", jrds_endpoint)

def check_dns_endpoint(region, automation, endpoint):
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    new_endpoint = None
    sock.settimeout(180) #180s
    if "*" in endpoint and automation is not None:
        new_endpoint = endpoint.replace("*", automation)
    elif "*" not in endpoint:
        new_endpoint = endpoint

    # print("url:"+new_endpoint)
    if new_endpoint is not None:
        try:
            response = sock.connect_ex((new_endpoint, 443))

            if response == 0:
                return True
            else:
                return False

        except Exception as ex:
            return False
    else:
        return False

def check_aa_dns_endpoints():
    rule_id = "Linux.AutomationDNSConnectivityCheck"
    rule_group_id = "connectivity"
    region = get_aa_region(workspace)
    # regiondict = {
    #     "australiasoutheast": "ase",
    #     "canadacentral": "cc",
    #     "southafricanorth": "san",
    #     "eastasia": "ea",
    #     "southeastasia": "sea",
    #     "australiacentral": "ac",
    #     "australiacentral2": "cbr2",
    #     "australiaeast": "ae",
    #     "brazilsouth": "brs",
    #     "brazilsoutheast": "brse",
    #     "westeurope": "we",
    #     "northeurope": "ne",
    #     "francecentral": "fc",
    #     "francesouth": "mrs",
    #     "centralindia": "cid",
    #     "southindia": "ma",
    #     "japaneast": "jpe",
    #     "japanwest": "jpw",
    #     "koreacentral": "kc",
    #     "koreasouth": "ps",
    #     "norwayeast": "noe",
    #     "norwaywest": "now",
    #     "switzerlandwest": "stzw",
    #     "uaecentral": "auh",
    #     "uaenorth": "uaen",
    #     "ukwest": "cw",
    #     "uksouth": "uks",
    #     "centralus": "cus",
    #     "eastus": "eus",
    #     "eastus2": "eus2",
    #     "northcentralus": "ncus",
    #     "southcentralus": "scus",
    #     "westcentralus": "wcus",
    #     "westus": "wus",
    #     "westus2": "wus2",
    #     "westus3": "usw3",
    #     "usgovvirginia": "usge",
    #     "usgovtexas": "ussc",
    #     "usgovarizona": "phx"
    # }
    # region = regiondict.get(region, "invalid or unsupported region")

    write_log_output(rule_id, rule_group_id, status_debug, empty_failure_reason, "TCP test only if automation related solution is enabled !!!")
    i = 0
    #if it's fairefax, endpoint ends by *azure-automation.us https://docs.microsoft.com/en-us/azure/automation/how-to/automation-region-dns-records#support-for-private-link
    #only test 1 us gov endpoint, will add additional endpoints
    if is_fairfax_region() is True:
        fairfax_dns_endpoints = ["*.webhook.?.azure-automation.us", "*.agentsvc.?.azure-automation.us", "*.jrds.?.azure-automation.us"]
        # fairfax_dns_endpoints = get_dns_endpoint(fairfax_dns_endpoints, region)
        for endpoint in fairfax_dns_endpoints:
            i += 1
            if "?" in endpoint or "?" in endpoint and automation is not None:
                endpoint = endpoint.replace("?", region).replace("*", automation)

            if check_dns_endpoint(region, automation, endpoint):
                write_log_output(rule_id + str(i), rule_group_id, status_passed, empty_failure_reason, "TCP test for {" + endpoint + "} (port 443) succeeded", endpoint)
            else:
                write_log_output(rule_id + str(i), rule_group_id, status_failed, empty_failure_reason, "TCP test for {" + endpoint + "} (port 443) failed", endpoint)
    else:
        automation_dns_endpoints = ["*.webhook.?.azure-automation.net", "*.agentsvc.?.azure-automation.net", "*.jrds.?.azure-automation.net"]
        # automation_dns_endpoints = get_dns_endpoint(automation_dns_endpoints, region)
        for endpoint in automation_dns_endpoints:
            i += 1
            if "?" in endpoint or "?" in endpoint and workspace is not None:
                endpoint = endpoint.replace("?", region).replace("*", automation)

            if check_dns_endpoint(region, automation, endpoint):
                write_log_output(rule_id + str(i), rule_group_id, status_passed, empty_failure_reason, "TCP test for {" + endpoint + "} (port 443) succeeded", endpoint)
            else:
                write_log_output(rule_id + str(i), rule_group_id, status_failed, empty_failure_reason, "TCP test for {" + endpoint + "} (port 443) failed, you need them to support private link https://docs.microsoft.com/en-us/azure/automation/how-to/automation-region-dns-records#support-for-private-link", endpoint)

def main(SA=None, EH=None, output_path=None, return_json_output="False"):
    if os.geteuid() != 0:
        print ("Please run this script as root")
        exit()

    # supported python version 2.4.x to 2.7.x and 3.x

    if(sys.version_info[0] == 2) and ((sys.version_info[1]<4) and (sys.version_info[1] > 7)):
        print("Unsupport python version:" + str(sys.version_info))
#       exit()

    # print("Starting Azure Log Analytics connectivity test.")
    urls = ["LA agent: https://docs.microsoft.com/en-us/azure/azure-monitor/agents/log-analytics-agent#network-requirements", 
            "Diagnostic: https://docs.microsoft.com/en-us/azure/azure-monitor/agents/diagnostics-extension-troubleshooting#is-data-getting-transferred",
            "Automation linked: https://docs.microsoft.com/en-us/azure/automation/automation-network-configuration#hybrid-runbook-worker-and-state-configuration",
            "Private link: https://docs.microsoft.com/en-us/azure/azure-monitor/logs/private-link-security#how-it-works"]
    print ("Before started, please kindly refer to below docs for network requirements:")
    for url in urls:
        print (url)
    
    print("")

    global workspace
    #workspace ID
    workspace = get_workspace()
    if workspace == None:
        print("Fail to find workspace ID, please check if your agent is well configured: https://docs.microsoft.com/en-us/azure/azure-monitor/agents/log-analytics-agent#installation-options")
        exit()

    get_machine_info()
    check_os_version()
    check_imds_connectivity()
    check_proxy_connectivity()
    check_log_analytics_endpoints()
    check_dsc_agent_endpoint()
    global automation
    automation = get_automation(workspace)
    
    if automation == None:
        print("This machine is not connected to Azure automation, skip automation connectivity check")
    else:
        check_aa_dns_endpoints()
        check_jrds_endpoint(workspace)
    
    if len(sys.argv) <= 1:
        for line in output:
            print (line)

    if len(sys.argv) > 1 and len(sys.argv) < 3:
        if sys.argv[1] is not None:
            SA = sys.argv[1]
            print("sa:"+SA)
            check_lad_endpoints(SA, EH)
            # check_lad_ssl_connectivity(SA, EH)
            for line in output:
                print (line)

    if len(sys.argv) > 2 and len(sys.argv) < 4:
        if sys.argv[1] is not None or sys.argv[2] is not None:
            SA = sys.argv[1]
            EH = sys.argv[2]
            print("sa:"+SA)
            print("eh:"+EH)
            check_lad_endpoints(SA, EH)
            # check_lad_ssl_connectivity(SA, EH)
            for line in output:
                print (line)

    if len(sys.argv) > 3:
        if sys.argv[1] is not None or sys.argv[2] is not None:
            SA = sys.argv[1]
            EH = sys.argv[2]
            # print("sa:"+SA)
            # print("eh:"+EH)
            check_lad_endpoints(SA, EH)
            # check_lad_ssl_connectivity(SA, EH)
        
        if return_json_output == "True":
            print (json.dumps([obj.__dict__ for obj in rule_info_list]))
        else:
            for line in output:
                print (line)

            if sys.argv[3] is not None:
                try:
                    #print("output:"+sys.argv[3])
                    output_path = sys.argv[3]
                    #print("output1:"+output_path)
                    os.makedirs(output_path)
                except OSError:
                    if not os.path.isdir(output_path):
                        raise 
                log_path = "%s/testconnection-%s.log" % (output_path, datetime.datetime.utcnow().isoformat())
                f = open(log_path, "w")
                f.write("".join(output))
                f.close()
                print ("Output is written to " + log_path)

if __name__ == "__main__":
    print ("start......")
    if len(sys.argv) > 3:
        # print(sys.argv[1])
        # print(sys.argv[2])
        # print(sys.argv[3])
        # print(sys.argv[4])
        main(sys.argv)
    elif len(sys.argv) > 2:
        # print(sys.argv[1])
        # print(sys.argv[2])
        main(sys.argv[1], sys.argv[2])
    elif len(sys.argv) > 1:
        # print(sys.argv[1])
        main(sys.argv[1])
    else:
        main()
