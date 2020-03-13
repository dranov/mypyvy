import argparse
import collections
import concurrent.futures
import dataclasses
from dataclasses import dataclass
from datetime import datetime
import os
from pathlib import Path
import subprocess
import sys
import threading

from typing import cast, Dict, IO, List, Optional

# This class is actually unused at runtime. We just use it to statically check for typos in accessing options.
class NightlyArgs:
    output_directory: str
    job_timeout: int
    mypyvy_path: Path
    no_run: bool
    no_analyze: bool

args: NightlyArgs = cast(NightlyArgs, None)

def parse_args() -> None:
    global args

    argparser = argparse.ArgumentParser()
    argparser.add_argument('output_directory', nargs='?',
                           help='name of directory where output is stored')
    argparser.add_argument('--job-timeout', default='60', type=int,
                           help='number of seconds to allow each job to run before killing it')
    argparser.add_argument('--mypyvy-path', type=Path,
                           help='path to mypyvy repository (default: /path/to/nightly.py/../..)')
    argparser.add_argument('--no-run', action='store_true',
                           help='do not run jobs, just analyze results in existing directory')
    argparser.add_argument('--no-analyze', action='store_true',
                           help='do not analyze the results of, just run them')

    args = cast(NightlyArgs, argparser.parse_args(sys.argv[1:]))

    if args.no_run and args.output_directory is None:
        print('--no-run requires output_directory to be passed')
        argparser.print_help()
        sys.exit(1)

    if args.no_run and args.no_analyze:
        print('passing --no-run and --no-analyze means there is nothing to do. exiting.')
        sys.exit(0)

    if args.mypyvy_path is None:
        args.mypyvy_path = Path(__file__).parent.parent

@dataclass
class Job:
    name: str
    mypyvy_cmdline_args: List[str]

def format_datetime(d: datetime) -> str:
    return d.strftime('%Y%m%d-%H%M%S')

JOB_LOG_DIR = 'job-logs'

class JobRunner:
    def __init__(self, output_dir_name: Optional[str] = None) -> None:
        self.start_time = datetime.now()
        if output_dir_name is None:
            output_dir_name = f"mypyvy-nightly-output-{format_datetime(self.start_time)}"
            self.output_dir = Path(output_dir_name)
            self.output_dir.mkdir()
            self.log_dir = self.output_dir / JOB_LOG_DIR
            self.log_dir.mkdir()
        else:
            self.output_dir = Path(output_dir_name)
            assert self.output_dir.is_dir()

        self.global_logfile = open(self.output_dir / 'run-jobs.log', 'w')
        print(f'output in {self.output_dir}')
        self.log_global('mypyvy nightly starting')
        self.log_global(f'start_time={self.start_time}')
        self.log_global(f'args={sys.argv}')
        self.log_global(f'parsed args: {args}')
        self.log_global(f'mypyvy commit {get_mypyvy_sha()}')
        self.log_global('')

        self.collect_jobs()

    def collect_jobs(self) -> None:
        self.log_global('jobs:')
        self.jobs = []
        for example_file in (args.mypyvy_path / 'examples').glob('*.pyv'):
            job = Job(example_file.stem, ['updr', '--log=info', '--log-time', str(example_file)])
            self.log_global(f'  {job}')
            self.jobs.append(job)
        self.log_global('')

    def log(self, msg: str, logfile: IO[str]) -> None:
        print(format_datetime(datetime.now()), msg, file=logfile)

    def log_global(self, msg: str) -> None:
        self.log(msg, logfile=self.global_logfile)

    def run_job(self, job: Job) -> None:
        with open(self.log_dir / (job.name + '.out'), 'w') as f_out, \
             open(self.log_dir / (job.name + '.err'), 'w') as f_err, \
             open(self.log_dir / (job.name + '.log'), 'w') as f_log:

            self.log(f'worker thread {threading.current_thread().name}', f_log)
            cmd = ['python3.8', '-u', str(args.mypyvy_path / 'src' / 'mypyvy.py')] + job.mypyvy_cmdline_args
            self.log(f'running command {" ".join(cmd)}', f_log)
            proc_start_time = datetime.now()
            try:
                proc = subprocess.run(cmd, stdout=f_out, stderr=f_err, text=True, timeout=args.job_timeout)
            except subprocess.TimeoutExpired:
                self.log('process timed out', f_log)
            else:
                self.log(f'proc returned {proc.returncode}', f_log)
            proc_end_time = datetime.now()
            self.log(f'{(proc_end_time - proc_start_time).total_seconds()} elapsed', f_log)

    def run_jobs(self) -> None:
        self.log_global('beginning to run mypyvy jobs')
        with concurrent.futures.ThreadPoolExecutor(max_workers=max((os.cpu_count() or 1) - 1, 1)) as executor:
            fs = {}
            self.log_global('submitting jobs to queue')
            for job in self.jobs:
                fs[executor.submit(self.run_job, job)] = job
            self.log_global('jobs queued. waiting for completions...')
            for f in concurrent.futures.as_completed(fs):
                assert f.done()
                job = fs[f]
                self.log_global(f'completed {job}')
        self.log_global('done running mypyvy jobs')

def get_mypyvy_sha() -> str:
    return subprocess.run(['git', 'show-ref', '-s', 'HEAD'],
                          check=True, cwd=args.mypyvy_path, capture_output=True, text=True).stdout

@dataclass
class Result:
    name: str
    exit_msg: str
    time_msg: str
    out_msg: Optional[str] = dataclasses.field(default=None, init=False)

    def __str__(self) -> str:
        return f'{self.exit_msg} {self.time_msg}{(" " + self.out_msg) if self.out_msg is not None else ""}'

def analyze_results(output_dir: str) -> None:
    files: Dict[str, Dict[str, Path]] = collections.defaultdict(dict)
    for filename in (Path(output_dir) / JOB_LOG_DIR).iterdir():
        files[filename.stem][filename.suffix] = filename

    results = collections.defaultdict(list)
    output = []
    max_stem_length = max(len(file) for file in files)
    for stem in sorted(files):
        fs = files[stem]
        output.append(f'{stem}:')
        for suff in sorted(fs):
            output.append(f'  {suff}')
            with open(fs[suff]) as f:
                lines = f.readlines()
                for line in lines[-min(len(lines), 10):]:
                    output.append(f'    {line.strip()}')
                if suff == '.log':
                    exit_msg = ' '.join(lines[-2].strip().split(' ')[1:])

                    time_msg = ' '.join(lines[-1].strip().split(' ')[1:])
                    result = Result(stem, exit_msg, time_msg)
                    results[exit_msg].append(result)
                elif suff == '.out':
                    assert result.name == stem
                    for line in lines:
                        l = line.strip()
                        if l == 'frame is safe and inductive. done!':
                            result.out_msg = 'safe'
                            break
                        elif l == 'abstract counterexample: the system has no ' \
                             'universal inductive invariant proving safety':
                            result.out_msg = 'abstractly unsafe'

    with (Path(output_dir) / 'analysis.log').open('w') as analysis_log:
        for exit_msg in sorted(results):
            rs = results[exit_msg]
            print(f'{exit_msg}:', file=analysis_log)
            for r in rs:
                print(f'  {r.name.ljust(max_stem_length)} {r}', file=analysis_log)

        print('', file=analysis_log)
        for line in output:
            print(line, file=analysis_log)

def main() -> None:
    parse_args()
    print(args)

    if not args.no_run:
        runner: Optional[JobRunner] = JobRunner(output_dir_name=args.output_directory)
        assert runner is not None
        runner.run_jobs()
    else:
        runner = None

    out_dir = args.output_directory
    if not out_dir:
        assert runner is not None
        out_dir = str(runner.output_dir)

    if not args.no_analyze:
        analyze_results(out_dir)

if __name__ == '__main__':
    main()